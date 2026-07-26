import LeanNonlinearArith.Kernel.QPoly
import LeanNonlinearArith.Kernel.Roots

/-!
# nla-12a (first brick) — real algebraic numbers (mini-`anum`)

The computational algebraic-number core the nlsat port assigns to
variables: Z3's `algebraic_numbers.cpp` scoped down to what
`nlsat_assignment` / `nlsat_interval_set` / `nlsat_evaluator` consume —
comparison, sign queries, and rational separation. **Untrusted** (same
trust shape as the rest of `Kernel/`): every consequence re-enters proofs
only through nla-09 bridge certificates, so a bug here surfaces as a
failed check, never unsoundness.

Representation: `rat q` (Z3 "basic" values stay exact rationals), or
`root p (a, b)` = the unique root of square-free `p` in the open interval
`(a, b)` with non-root **dyadic** endpoints (nla-26.1b; `isolateRootsD`
emits this shape). Cell invariants beyond that, maintained by `mkRoot`
(z3 `am::normalize`): zero is never strictly inside an isolating interval
(a straddling interval is snapped at 0, or the value IS 0 and becomes
basic), and cells sharing a defining polynomial come from the same
isolation run, so overlapping intervals ⇒ same root.

Comparison (`compare`, nla-26.3): the **unfueled** 1:1 port of
`am::compare` / `compare_core` (`algebraic_numbers.cpp:1889-2122`) —
interval disjointness, same-polynomial fast path, magnitude
equalization with rationality discovery, the interval-expansion
"Sturm workaround", and the Sturm–Tarski sign evaluation as the
deciding step. No fuel, no `.eq`-on-exhaustion default: every branch
terminates structurally (refinement counts are magnitude differences;
Sturm–Tarski always decides). This retires the previous gcd
common-root fast test and with it the nla-25.1 endpoint-root risk —
different-polynomial equality is decided by `V == 0`, not gcd root
counting.
-/

namespace LeanNonlinearArith.Kernel

open QPoly

/-- Real algebraic number (kernel representation). Invariants for
`root p a b` (maintained by constructors, relied on by everything):
`p` square-free with exactly one real root in `(a, b)`, `a < b`,
`eval p a ≠ 0 ≠ eval p b`, and `0 ∉ (a, b)` (z3 `am::normalize` — build
through `mkRoot`). Endpoints are dyadic (z3 `mpbq`). -/
inductive RAlg
  | rat (q : Rat)
  | root (p : QPoly) (a b : Mpbq)
deriving Repr, Inhabited, BEq

namespace RAlg

/-- z3 `m_min_magnitude = −min_mag`, `min_mag` default 16
(`algebraic_params.pyg`): refinement in the compare ladder stops
tightening once intervals reach width-magnitude `−16`. -/
def minMagnitude : Int := -16

/-- z3 `imp::magnitude(l, u)` (`algebraic_numbers.cpp:903`), verbatim:
an approximation of the interval size's binary magnitude. Precondition
(z3 SASSERT): the interval does not straddle zero — guaranteed for cells
built via `mkRoot`. The two sign branches of the source coincide under
`natAbs`, so the function is total anyway. -/
def intervalMagnitude (l u : Mpbq) : Int :=
  if l.k == u.k then Mpbq.magnitudeUb l
  else if l.isNonneg then
    (Nat.log2 u.num.natAbs : Int) - (Nat.log2 l.num.natAbs : Int)
      - u.k + l.k - u.k
  else
    -- mlog2(u) − mlog2(l) − u_k + l_k − u_k; mlog2 x = log2 (−x)
    (Nat.log2 u.num.natAbs : Int) - (Nat.log2 l.num.natAbs : Int)
      - u.k + l.k - u.k

/-- Smart constructor (z3 cell construction + `am::normalize`):
degree-1 polynomials collapse to their rational root (eager rational
discovery beyond degree 1 happens only through factorization in Z3,
which we don't port — declared; higher-degree rational roots are instead
discovered lazily by `refine1`'s midpoint-zero test, exactly as in
`am::refine`). A zero-straddling interval is normalized per
`upolynomial::normalize_interval_core`: if 0 is the root the value
becomes basic, otherwise the endpoint on 0's sign side snaps to 0. -/
def mkRoot (p : QPoly) (a b : Mpbq) : RAlg :=
  if p.size == 2 then
    -- c₀ + c₁·x ⇒ root = −c₀/c₁
    .rat (-(p.coeff 0) / p.coeff 1)
  else if a.isNeg && b.isPos then
    if eval p 0 == 0 then .rat 0    -- has_zero_roots: zero IS the root
    else
      let signA := evalSignAtD p a
      let signZ : Int := if eval p 0 < 0 then -1 else 1
      if signA == signZ then .root p (Mpbq.ofInt 0) b
      else .root p a (Mpbq.ofInt 0)
  else
    .root p a b

/-- Position of an isolated root relative to a rational `q` — z3
`compare(algebraic_cell, mpq)` (`algebraic_numbers.cpp:1910`): endpoint
checks, then the sign trick — `p(q) = 0` means `q` is THE root, and
otherwise the root is above `q` iff `p(q)` has the same sign as `p` at
the lower endpoint (`p` changes sign exactly once in the interval). -/
def compareRootRat (p : QPoly) (a b : Mpbq) (q : Rat) : Ordering :=
  if b.leRat q then .lt          -- α < b ≤ q
  else if a.geRat q then .gt     -- q ≤ a < α
  else
    let v := eval p q
    if v == 0 then .eq
    else
      let sq : Int := if v < 0 then -1 else 1
      if sq == evalSignAtD p a then .gt else .lt

/-- Sign of the algebraic number itself (−1 / 0 / 1). -/
def sign : RAlg → Int
  | .rat q => if q < 0 then -1 else if q == 0 then 0 else 1
  | .root p a b =>
    match compareRootRat p a b 0 with
    | .lt => -1
    | .eq => 0
    | .gt => 1

/-- Sign of a polynomial `g` at the algebraic point (Tarski query for the
root case, plain evaluation for rationals). -/
def signOfPolyAt (g : QPoly) : RAlg → Int
  | .rat q =>
    let v := eval g q
    if v < 0 then -1 else if v == 0 then 0 else 1
  | .root p a b => signAtRootD g p a b

/-- One refinement step (z3 `am::refine`, nla-26.5): identity on
rationals; on a `root`, one `refineCoreStepD` bisection — and when the
midpoint IS the root, the cell **becomes basic**: the exact rational
value is discovered and the representation normalizes to `.rat`
(z3 remark: "a root object may become basic when invoking this method,
since we may find the actual rational root. This can only happen when
non minimal polynomials are used to encode root objects."). -/
def refine1 : RAlg → RAlg
  | .rat q => .rat q
  | .root p a b =>
    match refineCoreStepD p (evalSignAtD p a) a b with
    | .inl (a', b') => .root p a' b'
    | .inr r => .rat r.toRat

/-- z3 `am::refine_until_prec`: refine a root cell until its width is
`< 1/2^prec` — the binary `lt_1div2k` gate (nla-26.6), replacing the
`Rat` width threshold. An exact midpoint hit converts to basic. -/
def refineUntilPrec (x : RAlg) (prec : Nat) : RAlg :=
  match x with
  | .rat q => .rat q
  | .root p a b =>
    match refineToPrecD p (evalSignAtD p a) a b prec with
    | .inl (a', b') => .root p a' b'
    | .inr r => .rat r.toRat

/-- z3 `imp::magnitude(cell)`: binary magnitude of the isolating
interval — the evaluator's refinement gate (nla-12b-ii). Basic values
are exact; Z3 only ever queries cells, so `minMagnitude` ("already
precise") is the natural reading for `.rat`. -/
def magnitude : RAlg → Int
  | .rat _ => minMagnitude
  | .root _ a b => intervalMagnitude a b

/-- z3 `am::int_lt` (`algebraic_numbers.cpp:2827`): an integer strictly
below the value — refined to width < 1/2 first, so the answer stays
near the value (`⌊lower⌋` for cells, `⌊v⌋ − 1` for basic values). -/
def intLt (x : RAlg) : Int :=
  match refineUntilPrec x 1 with
  | .rat q => Mpbq.ratFloorInt q - 1
  | .root _ a _ => Mpbq.floorInt a

/-- z3 `am::int_gt` (`algebraic_numbers.cpp:2840`): an integer strictly
above the value. -/
def intGt (x : RAlg) : Int :=
  match refineUntilPrec x 1 with
  | .rat q => Mpbq.ratCeilInt q + 1
  | .root _ _ b => Mpbq.ceilInt b

/-- z3 `am::separate` (`algebraic_numbers.cpp:2794`): given `x < y`,
refine until the isolating brackets clear each other (a became-basic
cell breaks the loop, and `select` re-dispatches on the new shape).
Terminates: distinct values ⇒ the halving brackets eventually separate. -/
partial def separate (x y : RAlg) : RAlg × RAlg :=
  match x, y with
  | .rat p, .root _ cl _ =>
    if cl.leRat p then
      match refine1 y with
      | y'@(.root _ _ _) => separate x y'
      | y' => (x, y')          -- curr became basic
    else (x, y)
  | .root _ _ pu, .rat c =>
    if pu.geRat c then
      match refine1 x with
      | x'@(.root _ _ _) => separate x' y
      | x' => (x', y)          -- prev became basic
    else (x, y)
  | .root _ _ pu, .root _ cl _ =>
    if Mpbq.ge pu cl then
      let x' := refine1 x
      let y' := refine1 y
      match x', y' with
      | .root _ _ _, .root _ _ _ => separate x' y'
      | _, _ => (x', y')       -- one became basic
    else (x, y)
  | _, _ => (x, y)             -- basic/basic: do nothing

/-- z3 `am::select` (`algebraic_numbers.cpp:2856`), nla-26.4: a "nice"
(few-bit dyadic) value strictly between `x < y` — separate the brackets,
then `select_small_core` on the four basic/algebraic shapes: open
rational bounds on basic sides, the (cleared) bracket endpoints on
algebraic sides. This is the witness picker's gap selection, replacing
`ratBetween`. -/
def select (x y : RAlg) : Rat :=
  let (x, y) := separate x y
  let w : Mpbq :=
    match x, y with
    | .rat p, .rat c => Mpbq.selectSmallCoreQQ p c
    | .rat p, .root _ cl _ => Mpbq.selectSmallCoreQD p cl
    | .root _ _ pu, .rat c => Mpbq.selectSmallCoreDQ pu c
    | .root _ _ pu, .root _ cl _ => Mpbq.selectSmallCoreDD pu cl
  w.toRat

/-- z3 `compare_core` (`algebraic_numbers.cpp:1929`) — both arguments
algebraic. Stages, each ending in the `COMPARE_INTERVAL` disjointness
check:

1. interval disjointness (cheap path);
2. same defining polynomial + overlapping intervals ⇒ same root
   (`compare_p`; sound by the same-isolation-run invariant);
3. *(z3's minimal-polynomial refine-forever branch is unreachable for
   us: it requires factorization, which sets `m_minimal` — we never do,
   matching `set(…, minimal := false)` at our construction sites)*;
4. magnitude equalization: refine the coarser cell down to
   `target = max(minMagnitude, min aM bM)`, then both to
   `minMagnitude`, one step at a time — any exact-root discovery
   converts that side to a rational and re-dispatches (z3
   `return compare(a, b)`);
5. "Sturm workaround" (z3 comment: Sturm sequences have open bugs, so
   first try separating refined *copies*): refine copies to width
   `< 1/2^40` (`get_interval` at precision 10, ×4 binary digits) and
   compare; skipped if either copy discovers its root exactly;
6. Sturm–Tarski: `V = TaQ(p₂, p₁; a₁, b₁)` = sign of `p₂` at `α₁`;
   `V = 0` ⇒ equal, else the sign of `p₂` at `b₂`'s lower endpoint
   orients the answer. -/
def compareCore (p1 : QPoly) (a1 b1 : Mpbq) (p2 : QPoly) (a2 b2 : Mpbq) :
    Ordering := Id.run do
  -- COMPARE_INTERVAL
  if Mpbq.le b1 a2 then return .lt
  if Mpbq.ge a1 b2 then return .gt
  -- compare_p: same polynomial + overlap ⇒ same root
  if p1 == p2 then return .eq
  let s1 := evalSignAtD p1 a1
  let s2 := evalSignAtD p2 a2
  let mut x1 := a1; let mut y1 := b1
  let mut x2 := a2; let mut y2 := b2
  -- magnitude equalization
  let aM := intervalMagnitude x1 y1
  let bM := intervalMagnitude x2 y2
  let targetM := max minMagnitude (min aM bM)
  if bM > targetM then
    match refineStepsD p2 s2 x2 y2 (bM - targetM).toNat with
    | .inr r => return compareRootRat p1 x1 y1 r.toRat
    | .inl (x2', y2') =>
      x2 := x2'; y2 := y2'
      if Mpbq.le y1 x2 then return .lt
      if Mpbq.ge x1 y2 then return .gt
  if aM > targetM then
    match refineStepsD p1 s1 x1 y1 (aM - targetM).toNat with
    | .inr r => return (compareRootRat p2 x2 y2 r.toRat).swap
    | .inl (x1', y1') =>
      x1 := x1'; y1 := y1'
      if Mpbq.le y1 x2 then return .lt
      if Mpbq.ge x1 y2 then return .gt
  if targetM > minMagnitude then
    for _ in [0:(targetM - minMagnitude).toNat] do
      match refineCoreStepD p1 s1 x1 y1 with
      | .inr r => return (compareRootRat p2 x2 y2 r.toRat).swap
      | .inl (x1', y1') =>
        x1 := x1'; y1 := y1'
        match refineCoreStepD p2 s2 x2 y2 with
        | .inr r => return compareRootRat p1 x1 y1 r.toRat
        | .inl (x2', y2') =>
          x2 := x2'; y2 := y2'
          if Mpbq.le y1 x2 then return .lt
          if Mpbq.ge x1 y2 then return .gt
  -- Sturm workaround: separate refined copies (precision 10 ⇒ 40 bits)
  match refineToPrecD p1 s1 x1 y1 40, refineToPrecD p2 s2 x2 y2 40 with
  | .inl (la, ua), .inl (lb, ub) =>
    if Mpbq.gt la ub then return .gt
    if Mpbq.lt ua lb then return .lt
  | _, _ => pure ()
  -- expensive case: Sturm–Tarski
  let V : Int := tarskiQuery p2 p1 x1.toRat y1.toRat
  if V == 0 then return .eq
  if (V < 0) == (s2 < 0) then return .lt
  return .gt

/-- Total comparison — z3 `am::compare` dispatch
(`algebraic_numbers.cpp:2108`). Unfueled: see `compareCore`. -/
def compare (x y : RAlg) : Ordering :=
  match x, y with
  | .rat p, .rat q => if p < q then .lt else if p == q then .eq else .gt
  | .root p a b, .rat q => compareRootRat p a b q
  | .rat q, .root p a b => (compareRootRat p a b q).swap
  | .root p1 a1 b1, .root p2 a2 b2 => compareCore p1 a1 b1 p2 a2 b2

def lt (x y : RAlg) : Bool := compare x y == .lt
def le (x y : RAlg) : Bool := compare x y != .gt

end RAlg

end LeanNonlinearArith.Kernel
