import LeanNonlinearArith.Kernel.BivPoly
import LeanNonlinearArith.Kernel.CellStore
import LeanNonlinearArith.Kernel.Factor

/-!
# nla-29.2/29.3 — anum arithmetic: `mk_binary` engine and the field ops (untrusted)

The op-by-op algebraic-number arithmetic of `algebraic_numbers.cpp`,
ported 1:1 against the source. This is what the `q ≡ 0` fallbacks of
`isolateRootsAt` (nla-29.5) need, and more generally what any anum-valued
evaluation (`imp::eval`, nla-29.4) composes.

Contents:

* `mkBinary` (:1210) — the resultant-composition engine: build the
  result polynomial (`mk_add_polynomial`/`mk_mul_polynomial` shapes via
  `BivPoly.resultantElimY`), factor it (nla-27), Sturm-select the factor
  owning the result root, refining the operands until the selection is
  unique. `save_intervals`/`restore_if_too_small` semantics on both
  exits (z3's destructor restores on every path — the duplicate
  `saved_a` call at :1285-1286 is a harmless no-op, saved_b is restored
  by its destructor).
* `setCore` (:1150) — zero-root snap via Sturm variations at zero,
  zero-root stripping, `isolating2refinable`, became-rational on exact
  hits.
* The ops (:1584-1883): `add`/`sub`/`mul` dispatch tables verbatim,
  `neg` (`p_minus_x`), `inv` (`refine_nz_bound` first, then
  `p_1_div_x` + rational-interval inversion), `div = inv ∘ mul`.
* `CellStore` lifts (`addC` etc.) — the owner-level threading of the
  nla-28 discipline: refinements and became-basic conversions persist
  in place; results are freshly allocated cells.

Two declared z3-bug-side treatments (verdict-preserving; z3's own
behavior is a latent bug or a crash, not a verdict):

1. `add`/`mul` algebraic×basic: when `convert_q2bq_interval` reports an
   exact root (its `false`), z3 logs "conversion failed" and calls
   `set` with a stale upper bound (:1629/:1742). The result VALUE is
   that dyadic root; we return `.rat` of it.
2. `inv`: z3 *throws* when the inversion's convert hits the exact root
   (:1858). Same treatment: became-rational. z3's throw aborts the
   whole nlsat call; returning the rational can only let us continue
   where z3 fails — never the reverse (parity of verdicts is upward).

Same trust shape as the rest of `Kernel/`: untrusted search-side code.
-/

namespace LeanNonlinearArith.Kernel

open QPoly

namespace RAlg

/-- z3 `is_zero(numeral)`: a basic zero. Root cells are never value-zero
(the `mkRoot` invariant makes value-0 basic at construction). -/
def isZeroV : RAlg → Bool
  | .rat q => q == 0
  | .root .. => false

/-- z3 `save_intervals::restore_if_too_small` (:1122): if the cell is
still algebraic and its interval magnitude dropped below
`minMagnitude`, restore the snapshot; became-basic conversions stick
(z3: `if (m_num.is_basic()) return`). -/
def restoreIfTooSmall (snap cur : RAlg) : RAlg :=
  match cur with
  | .rat _ => cur
  | .root _ a b _ =>
    if intervalMagnitude a b < minMagnitude then snap else cur

/-- z3 `set_core` (:1150) on the selected factor: zero-straddle snap via
Sturm variations at zero (`sign_variations_at_zero(seq)`), then
zero-root strip + `isolating2refinable`; an exact-root hit becomes
rational. `lV`/`uV` are the variation counts of `seq` (the Sturm chain
of `p`) at `ri`'s endpoints, from the `mkBinary` scan. -/
def setCore (p : QPoly) (ri : MpbqI) (seq : Array QPoly) (lV uV : Int)
    (minimal : Bool) : RAlg :=
  if ri.containsZero && hasZeroRoots p then
    -- zero is a root of p, and ri is an isolating interval containing
    -- zero: the result IS rational 0 (z3 :1153-1158)
    .rat 0
  else
    let (lo, hi) :=
      if ri.containsZero then
        -- snap the endpoint on 0's side (z3 :1160-1169)
        let zV : Int := signVarAt seq 0
        if lV == zV then (Mpbq.ofInt 0, ri.hi)   -- root in the second half
        else (ri.lo, Mpbq.ofInt 0)               -- root in the first half
      else (ri.lo, ri.hi)
    let nzP := if hasZeroRoots p then removeZeroRoots p else p
    match isolating2Refinable nzP lo hi with
    | .inr r => .rat r.toRat          -- found actual root
    | .inl (a, b) => mkRoot nzP a b minimal

/-- The three functor bundles of z3's `mk_binary` template
(`MkResultPoly`/`MkResultInterval`/`MkBasic`, :1202-1207). `mkBasic` is
the full op dispatch (`add_proc`/`sub_proc`/`mul_proc`) for the
became-basic re-dispatch. -/
structure MkBinaryOps where
  mkPoly : QPoly → QPoly → QPoly
  mkInterval : MpbqI → MpbqI → MpbqI
  mkBasic : RAlg → RAlg → RAlg × RAlg × RAlg

/-- z3 `mk_binary` (:1210): resultant-composed defining polynomial →
factor (nla-27) → per-factor Sturm chains → the discard/target scan
(`V ≤ 0` discard, `V == 1` target, else keep) → success via `setCore`,
else refine both operands and rescan. Refinement is short-circuited
exactly as z3's `!refine(a) || !refine(b)`: when `a` becomes basic, `b`
is NOT refined that round; either became-basic exits through `mkBasic`
(the full op). The Sturm chains are our `|lc|`-normalized `sturmChain` —
positive rescaling preserves variation counts, so the `V`s are
value-identical to z3's `sturm_seq` counts. Result order is
`(c, a', b')` (nla-28 tuple threading). -/
partial def mkBinary (ops : MkBinaryOps) (a b : RAlg) : RAlg × RAlg × RAlg :=
  match a, b with
  | .root pa _ _ _, .root pb _ _ _ =>
    let p := ops.mkPoly pa pb
    let (fullFact, fs) := factor (QPoly.toZPoly p)
    let factors : Array QPoly := fs.factors.map fun (fp, _) => ZPoly.toQPoly fp
    let seqs0 : Array (Option (Array QPoly)) := factors.map fun f => some (sturmChain f)
    let rec loop (x y : RAlg) (seqs : Array (Option (Array QPoly))) :
        RAlg × RAlg × RAlg :=
      match x, y with
      | .root _ xa xb _, .root _ ya yb _ =>
        let ri := ops.mkInterval ⟨xa, xb⟩ ⟨ya, yb⟩
        let (numRem, targetI, targetLV, targetUV, seqs') := Id.run do
          let mut numRem := 0
          let mut targetI := seqs.size   -- UINT_MAX analogue
          let mut targetLV : Int := 0
          let mut targetUV : Int := 0
          let mut seqs := seqs
          for i in [0:seqs.size] do
            if let some ch := seqs[i]! then
              let lV := signVarAt ch ri.lo.toRat
              let uV := signVarAt ch ri.hi.toRat
              let V : Int := (lV : Int) - (uV : Int)
              if V ≤ 0 then
                seqs := seqs.set! i none      -- factor does not contain the root
              else if V == 1 then
                targetI := i; targetLV := lV; targetUV := uV
                numRem := numRem + 1
              else
                numRem := numRem + 1
          return (numRem, targetI, targetLV, targetUV, seqs)
        if numRem == 1 && targetI != seqs'.size then
          let x' := restoreIfTooSmall a x
          let y' := restoreIfTooSmall b y
          let c := setCore factors[targetI]! ri (seqs'[targetI]!.get!)
            targetLV targetUV fullFact
          (c, x', y')
        else
          match refine1 x with
          | x₁@(.rat _) =>
            -- a became basic: restore both, re-dispatch the full op
            -- (z3 does NOT refine b this round — short-circuit ||)
            ops.mkBasic (restoreIfTooSmall a x₁) (restoreIfTooSmall b y)
          | x₁ =>
            match refine1 y with
            | y₁@(.rat _) =>
              ops.mkBasic (restoreIfTooSmall a x₁) (restoreIfTooSmall b y₁)
            | y₁ => loop x₁ y₁ seqs'
      | _, _ => ops.mkBasic x y
    loop a b seqs0
  | _, _ => ops.mkBasic a b

/-! ## The mixed algebraic↔basic paths -/

/-- z3 `add<IsAdd>(algebraic_cell *, basic_cell *, c)` (:1598): defining
polynomial `translate_q(p, ∓q)` (roots shift by `±q`), interval shifted
by `±q` — dyadic fast path when `q` converts, `convert_q2bq_interval`
fallback otherwise. Minimality is preserved (z3 comment :1640). For
the `.inl` (exact-root) case of the fallback see the file header. -/
def addAlgebraicBasic (isAdd : Bool) (p : QPoly) (a b : Mpbq) (m : Bool)
    (q : Rat) : RAlg :=
  let shift := if isAdd then q else -q
  let p' := translateQ p (-shift)
  match Mpbq.ofRat shift with
  | (qd, true) => mkRoot p' (Mpbq.add a qd) (Mpbq.add b qd) m
  | _ =>
    match convertQ2BqInterval p' (a.toRat + shift) (b.toRat + shift) with
    | .inl r => .rat r.toRat
    | .inr (c, d) => mkRoot p' c d m

/-- z3 `mul(algebraic_cell *, basic_cell *, c)` (:1706): defining
polynomial `compose_p_q_x(p, 1/q)` (roots scale by `q`), interval
endpoints scaled by `q` with the negative-scalar swap; same fallback
shape as `addAlgebraicBasic`. Precondition `q ≠ 0` (the zero case is
dispatched before this is reached). -/
def mulAlgebraicBasic (p : QPoly) (a b : Mpbq) (m : Bool) (q : Rat) : RAlg :=
  let p' := composePQX p (1 / q)
  match Mpbq.ofRat q with
  | (qd, true) =>
    let l := Mpbq.mul a qd
    let u := Mpbq.mul b qd
    let (l, u) := if q < 0 then (u, l) else (l, u)
    mkRoot p' l u m
  | _ =>
    let il := a.toRat * q
    let iu := b.toRat * q
    let (il, iu) := if q < 0 then (iu, il) else (il, iu)
    match convertQ2BqInterval p' il iu with
    | .inl r => .rat r.toRat
    | .inr (c, d) => mkRoot p' c d m

/-- z3 `neg(numeral)` (:1776): `p_minus_x` + interval negation. -/
def neg : RAlg → RAlg
  | .rat q => .rat (-q)
  | .root p a b m => mkRoot (pMinusX p) (Mpbq.neg b) (Mpbq.neg a) m

/-! ## The ops -/

/-- z3 `add(numeral, numeral, c)` (:1644): zero shortcuts, basic+basic,
the mixed translate path, algebraic+algebraic via `mkBinary` with
`resultant_y(pa(x−y), pb(y))`. -/
partial def add (a b : RAlg) : RAlg × RAlg × RAlg :=
  if isZeroV a then (b, a, b)
  else if isZeroV b then (a, a, b)
  else
    match a, b with
    | .rat qa, .rat qb => (.rat (qa + qb), a, b)
    | .rat q, .root p aa ba m => (addAlgebraicBasic true p aa ba m q, a, b)
    | .root p aa ba m, .rat q => (addAlgebraicBasic true p aa ba m q, a, b)
    | .root .., .root .. =>
      mkBinary ⟨fun pa pb => BivPoly.resultantElimY (BivPoly.composeXMinusY pa) pb,
        MpbqI.add, add⟩ a b

/-- z3 `sub(numeral, numeral, c)` (:1669): `0 − b = −b`, `a − 0 = a`;
basic−algebraic goes through the `IsAdd := false` mixed path and a final
`neg` (:1684-1688); algebraic−algebraic via `mkBinary` with
`resultant_y(pa(x+y), pb(y))` and interval subtraction. -/
partial def sub (a b : RAlg) : RAlg × RAlg × RAlg :=
  if isZeroV a then (neg b, a, b)
  else if isZeroV b then (a, a, b)
  else
    match a, b with
    | .rat qa, .rat qb => (.rat (qa - qb), a, b)
    | .rat q, .root p aa ba m => (neg (addAlgebraicBasic false p aa ba m q), a, b)
    | .root p aa ba m, .rat q => (addAlgebraicBasic false p aa ba m q, a, b)
    | .root .., .root .. =>
      mkBinary ⟨fun pa pb => BivPoly.resultantElimY (BivPoly.composeXPlusY pa) pb,
        MpbqI.sub, sub⟩ a b

/-- z3 `mul(numeral, numeral, c)` (:1756): either zero ⇒ basic 0;
basic×basic; the mixed compose path; algebraic×algebraic via `mkBinary`
with `resultant_y(y^n·pa(x/y), pb(y))` and interval multiplication. -/
partial def mul (a b : RAlg) : RAlg × RAlg × RAlg :=
  if isZeroV a || isZeroV b then (.rat 0, a, b)
  else
    match a, b with
    | .rat qa, .rat qb => (.rat (qa * qb), a, b)
    | .rat q, .root p aa ba m => (mulAlgebraicBasic p aa ba m q, a, b)
    | .root p aa ba m, .rat q => (mulAlgebraicBasic p aa ba m q, a, b)
    | .root .., .root .. =>
      mkBinary ⟨fun pa pb => BivPoly.resultantElimY (BivPoly.composeXDivY pa) pb,
        MpbqI.mul, mul⟩ a b

/-- z3 `refine_nz_bound` (:1794): walk a zero-valued interval endpoint
inward by halving until its sign matches the cell's endpoint sign — an
exact hit discovers the rational root (became basic). `sign_l` is the
sign of `p` at the lower endpoint (z3 reads its cache; we recompute —
same value). -/
partial def refineNzBound : RAlg → RAlg
  | .rat q => .rat q
  | x@(.root p a b m) =>
    if !a.isZero && !b.isZero then x
    else
      let signL := evalSignAtD p a
      if a.isZero then
        let rec walkL (bd : Mpbq) : RAlg :=
          let bd := Mpbq.div2 bd
          let s := evalSignAtD p bd
          if s == 0 then .rat bd.toRat
          else if s == signL then .root p bd b m
          else walkL bd
        walkL b
      else
        -- upper is zero; z3 walks it down from `a` with target −sign_l
        let rec walkU (bd : Mpbq) : RAlg :=
          let bd := Mpbq.div2 bd
          let s := evalSignAtD p bd
          if s == 0 then .rat bd.toRat
          else if s == -signL then .root p a bd m
          else walkU bd
        walkU a

/-- z3 `inv(numeral)` (:1835): `refine_nz_bound` first, then `p_1_div_x`
with the rational interval inversion `(1/upper, 1/lower)` tightened back
to dyadic by `convert_q2bq_interval`. Precondition: value ≠ 0 (z3
throws on zero; our callers pre-discharge it). On the convert's
exact-root case z3 throws — see the file header for our treatment. -/
partial def inv : RAlg → RAlg
  | .rat q => .rat (1 / q)
  | x@(.root ..) =>
    match refineNzBound x with
    | .rat q => .rat (1 / q)
    | .root p a b m =>
      let p' := p1DivX p
      match convertQ2BqInterval p' (1 / b.toRat) (1 / a.toRat) with
      | .inl r => .rat r.toRat
      | .inr (c, d) => mkRoot p' c d m

/-- z3 `div(numeral, numeral, c)` (:1868): `inv` on a COPY of the divisor
(z3 `set(invb, b); inv(invb)` — `b` itself is never mutated), then `mul`.
Precondition: `b ≠ 0`. -/
partial def div (a b : RAlg) : RAlg × RAlg × RAlg :=
  let binv := inv b
  let (c, a', _) := mul a binv
  (c, a', b)

/-- z3 `x − y^k` as a bivariate (the `mk_power_polynomial` shape,
:1430). -/
private def xMinusYPow (k : Nat) : BivPoly := Id.run do
  let mut r : BivPoly := Array.replicate (k + 1) #[]
  r := r.set! 0 QPoly.X
  r := r.set! k (QPoly.C (-1))
  return r

/-- The two functor bundles of z3's `mk_unary` template (analogue of
`MkBinaryOps`; `mkBasic` returns only the result — the became-basic
operand is the restored input itself). -/
structure MkUnaryOps where
  mkPoly : QPoly → QPoly
  mkInterval : MpbqI → MpbqI
  mkBasic : RAlg → RAlg

/-- z3 `mk_unary` (:1292): same engine as `mkBinary`, single operand —
`save_intervals` on `a` only, restore on both exits (z3's duplicate
`saved_a` call at :1359 and the destructor agree here). Returns
`(result, refinedA)` for the nla-28 write-back. -/
partial def mkUnary (ops : MkUnaryOps) (a : RAlg) : RAlg × RAlg :=
  match a with
  | .root pa _ _ _ =>
    let p := ops.mkPoly pa
    let (fullFact, fs) := factor (QPoly.toZPoly p)
    let factors : Array QPoly := fs.factors.map fun (fp, _) => ZPoly.toQPoly fp
    let seqs0 : Array (Option (Array QPoly)) := factors.map fun f => some (sturmChain f)
    let rec loop (x : RAlg) (seqs : Array (Option (Array QPoly))) : RAlg × RAlg :=
      match x with
      | .root _ xa xb _ =>
        let ri := ops.mkInterval ⟨xa, xb⟩
        let (numRem, targetI, targetLV, targetUV, seqs') := Id.run do
          let mut numRem := 0
          let mut targetI := seqs.size
          let mut targetLV : Int := 0
          let mut targetUV : Int := 0
          let mut seqs := seqs
          for i in [0:seqs.size] do
            if let some ch := seqs[i]! then
              let lV := signVarAt ch ri.lo.toRat
              let uV := signVarAt ch ri.hi.toRat
              let V : Int := (lV : Int) - (uV : Int)
              if V ≤ 0 then
                seqs := seqs.set! i none
              else if V == 1 then
                targetI := i; targetLV := lV; targetUV := uV
                numRem := numRem + 1
              else
                numRem := numRem + 1
          return (numRem, targetI, targetLV, targetUV, seqs)
        if numRem == 1 && targetI != seqs'.size then
          (setCore factors[targetI]! ri (seqs'[targetI]!.get!)
            targetLV targetUV fullFact,
           restoreIfTooSmall a x)
        else
          match refine1 x with
          | x₁@(.rat _) =>
            let x' := restoreIfTooSmall a x₁
            (ops.mkBasic x', x')
          | x₁ => loop x₁ seqs'
      | _ => (ops.mkBasic x, x)
    loop a seqs0
  | _ => (ops.mkBasic a, a)

/-- z3 `power(numeral, k, b)` (:1559): `k = 0 ⇒ 1`, `k = 1 ⇒ a`,
`a = 0 ⇒ 0`, basic ⇒ rational power, else `mkUnary` with
`resultant_y(x − y^k, pa(y))` and the interval power. Returns
`(result, refinedA)` (the stored-cell write-back for the const_cast
sites, e.g. `t_eval_core`'s `vm.power(x2v(x), …)`). -/
partial def power (a : RAlg) (k : Nat) : RAlg × RAlg :=
  if k == 0 then (.rat 1, a)
  else if k == 1 then (a, a)
  else if isZeroV a then (.rat 0, a)
  else
    match a with
    | .rat q => (.rat (q ^ k), a)
    | .root .. =>
      mkUnary ⟨fun pa => BivPoly.resultantElimY (xMinusYPow k) pa,
        fun i => MpbqI.pow i k,
        fun x => (power x k).1⟩ a

end RAlg

/-! ## CellStore lifts (owner-level threading, nla-28 discipline) -/

namespace CellStore

/-- `RAlg.add` on stored cells: refinements persist; result is a fresh
cell (z3 `set(c, …)` on an output numeral). -/
def addC (x y : CellId) : CellM CellId := do
  let a ← read x
  let b ← read y
  let (c, a', b') := RAlg.add a b
  write x a'
  write y b'
  fresh c

/-- `RAlg.sub` on stored cells. -/
def subC (x y : CellId) : CellM CellId := do
  let a ← read x
  let b ← read y
  let (c, a', b') := RAlg.sub a b
  write x a'
  write y b'
  fresh c

/-- `RAlg.mul` on stored cells. -/
def mulC (x y : CellId) : CellM CellId := do
  let a ← read x
  let b ← read y
  let (c, a', b') := RAlg.mul a b
  write x a'
  write y b'
  fresh c

/-- `RAlg.neg` in place (z3 `neg(numeral &)` mutates the numeral). -/
def negC (x : CellId) : CellM Unit := do
  modifyCell x RAlg.neg

/-- `RAlg.inv` in place (z3 `inv(numeral &)` mutates the numeral).
Precondition: value ≠ 0. -/
def invC (x : CellId) : CellM Unit := do
  modifyCell x RAlg.inv

/-- `RAlg.div` on stored cells (divisor not mutated, as z3). -/
def divC (x y : CellId) : CellM CellId := do
  let a ← read x
  let b ← read y
  let (c, a', b') := RAlg.div a b
  write x a'
  write y b'
  fresh c

end CellStore

end LeanNonlinearArith.Kernel
