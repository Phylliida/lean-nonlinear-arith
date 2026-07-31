import LeanNonlinearArith.Kernel.QPoly
import LeanNonlinearArith.Kernel.Roots
import LeanNonlinearArith.Kernel.Factor

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

**Statefulness (nla-28):** Z3's anum ops MUTATE their operands and the
refinement persists in solver state — `compare_core` takes `numeral &`
and refines both sides; `is_rational` refines and
can `set(a, candidate)` the value to a discovered rational
(`algebraic_numbers.cpp:285`); `select`/`separate` take `numeral &`.
(nla-32 re-anchor: `int_lt`/`int_gt` are PURE at 4.12.5 — the
`const_cast` refine-to-precision-1 in them is a post-4.12.5 addition,
not ported.)
The faithful functional image (DESIGN-endgame §2.1, Q2): every refining
op returns its (possibly refined) argument(s) alongside the result, and
callers that store cells (interval sets now, the solver assignment at
12c) thread the updated cells back into their store. Ops that never
refine (`sign`, `signOfPolyAt`, `magnitude`, root-vs-rational compare,
`intLt`/`intGt`) stay pure.
-/

namespace LeanNonlinearArith.Kernel

open QPoly

/-- Real algebraic number (kernel representation). Invariants for
`root p a b` (maintained by constructors, relied on by everything):
`p` square-free with exactly one real root in `(a, b)`, `a < b`,
`eval p a ≠ 0 ≠ eval p b`, and `0 ∉ (a, b)` (z3 `am::normalize` — build
through `mkRoot`). Endpoints are dyadic (z3 `mpbq`). `minimal` is z3's
`m_minimal` cell flag (nla-27): true when the defining polynomial is
known irreducible — set by `isolateRoots` from the factorization's
completeness flag, and implies `m_not_rational` (a non-linear minimal
polynomial has no rational root). -/
inductive RAlg
  | rat (q : Rat)
  | root (p : QPoly) (a b : Mpbq) (minimal : Bool := false)
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
degree-1 polynomials collapse to their rational root (with
factorization — nla-27 — rational roots surface eagerly as linear
factors, so this and the zero-straddle snap are safety nets, as are
default-Z3's radical-only became-basic paths). A zero-straddling
interval is normalized per `upolynomial::normalize_interval_core`: if
0 is the root the value becomes basic, otherwise the endpoint on 0's
sign side snaps to 0. `minimal` is z3's `m_minimal` (the factorization
completeness flag at cell construction). -/
def mkRoot (p : QPoly) (a b : Mpbq) (minimal : Bool := false) : RAlg :=
  if p.size == 2 then
    -- c₀ + c₁·x ⇒ root = −c₀/c₁
    .rat (-(p.coeff 0) / p.coeff 1)
  else if a.isNeg && b.isPos then
    if eval p 0 == 0 then .rat 0    -- has_zero_roots: zero IS the root
    else
      let signA := evalSignAtD p a
      let signZ : Int := if eval p 0 < 0 then -1 else 1
      if signA == signZ then .root p (Mpbq.ofInt 0) b minimal
      else .root p a (Mpbq.ofInt 0) minimal
  else
    .root p a b minimal


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
  | .root p a b _ =>
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
  | .root p a b _ => signAtRootD g p a b

/-- One refinement step (z3 `am::refine`, nla-26.5): identity on
rationals; on a `root`, one `refineCoreStepD` bisection — and when the
midpoint IS the root, the cell **becomes basic**: the exact rational
value is discovered and the representation normalizes to `.rat`
(z3 remark: "a root object may become basic when invoking this method,
since we may find the actual rational root. This can only happen when
non minimal polynomials are used to encode root objects."). -/
def refine1 : RAlg → RAlg
  | .rat q => .rat q
  | .root p a b m =>
    match refineCoreStepD p (evalSignAtD p a) a b with
    | .inl (a', b') => .root p a' b' m
    | .inr r => .rat r.toRat

/-- z3 `am::refine_until_prec`: refine a root cell until its width is
`< 1/2^prec` — the binary `lt_1div2k` gate (nla-26.6), replacing the
`Rat` width threshold. An exact midpoint hit converts to basic. -/
def refineUntilPrec (x : RAlg) (prec : Nat) : RAlg :=
  match x with
  | .rat q => .rat q
  | .root p a b m =>
    match refineToPrecD p (evalSignAtD p a) a b prec with
    | .inl (a', b') => .root p a' b' m
    | .inr r => .rat r.toRat

/-- z3 `imp::magnitude(cell)`: binary magnitude of the isolating
interval — the evaluator's refinement gate (nla-12b-ii). Basic values
are exact; Z3 only ever queries cells, so `minMagnitude` ("already
precise") is the natural reading for `.rat`. -/
def magnitude : RAlg → Int
  | .rat _ => minMagnitude
  | .root _ a b _ => intervalMagnitude a b

/-- z3 **4.12.5** `am::int_lt`: an integer strictly below the value
(`⌊v⌋ − 1` for basic values, `⌊lower⌋` read off the CURRENT dyadic
bound for cells). PURE: 4.12.5 does not refine or mutate the operand
here — the `refine_until_prec(a, 1)` + `const_cast` is a post-4.12.5
addition (nla-32 re-anchor; the tuple return of nla-28 is gone with
it). -/
def intLt : RAlg → Int
  | .rat q => Mpbq.ratFloorInt q - 1
  | .root _ a _ _ => Mpbq.floorInt a

/-- z3 **4.12.5** `am::int_gt`: an integer strictly above the value
(`⌈v⌉ + 1` for basic, `⌈upper⌉` for cells — valid because a cell's
dyadic upper bound strictly exceeds its irrational value). Pure, same
re-anchor as `intLt`. -/
def intGt : RAlg → Int
  | .rat q => Mpbq.ratCeilInt q + 1
  | .root _ _ b _ => Mpbq.ceilInt b

/-- z3 `imp::is_rational` (`algebraic_numbers.cpp:285`): rational-root-theorem
discovery. Refine to width `< 1/2^(log2|aₙ|+1)` so that `|aₙ|·(l,u)` contains
at most one integer, then the unique candidate `⌊u·|aₙ|⌋/|aₙ|` is the value
iff it lies above `l` and is a root; a hit **becomes basic**
(`set(a, candidate)`). z3's polynomials are ℤ-coefficient; ours are ℚ
(declared QPoly divergence, bridged at `ofQPoly`), so `aₙ` is the leading
coefficient after positive denominator-clearing (roots/signs unchanged — the
CertGen scaling pattern). `save_intervals::restore_if_too_small` is ported: on
a miss, an interval refined below `minMagnitude` magnitude is restored to its
input width (a became-basic conversion always sticks). The `m_not_rational`
cache flag is not stored: instead, with nla-27 the `minimal` field plays
its role — cells built by `isolateRoots` from a complete factorization
are irreducible, hence irrational, and short-circuit here exactly like
z3's `m_not_rational` check (`mk_algebraic_cell` sets the flag whenever
`m_minimal` holds). nla-28: returns the refined (or converted) cell
alongside the verdict. -/
def isRational : RAlg → Bool × RAlg
  | .rat q => (true, .rat q)
  | x@(.root _ _ _ true) => (false, x)   -- m_not_rational: minimal ⇒ irrational
  | x@(.root p _ _ false) =>
    -- positive denominator-clearing scale ⇒ ℤ leading coefficient `aₙ`
    let d : Nat := p.foldl (fun acc c => Nat.lcm acc c.den) 1
    let aN : Int := (lc p).num * ((d / (lc p).den : Nat) : Int)
    let absAN : Nat := aN.natAbs
    let k := Nat.log2 absAN + 1
    match refineUntilPrec x k with
    | .rat q => (true, .rat q)      -- became basic during refinement
    | x'@(.root _ a' b' _) =>
      -- ⌊b'·|aₙ|⌋ : floor of num·2^{−k'}·|aₙ|
      let zcand := ((absAN : Int) * b'.num).fdiv ((1 <<< b'.k : Nat) : Int)
      let cand := mkRat zcand absAN
      if a'.ltRat cand && eval p cand == 0 then
        (true, .rat cand)           -- set(a, candidate): becomes basic
      else
        -- restore_if_too_small: keep the input interval if over-refined
        if intervalMagnitude a' b' < minMagnitude then (false, x)
        else (false, x')

/-- z3 `am::separate` (`algebraic_numbers.cpp:2794`): given `x < y`,
refine until the isolating brackets clear each other.

**Declared divergence from the literal source (F1 review fix,
2026-07-26): on a became-basic cell we re-dispatch `separate` on the
new shapes instead of breaking.** Z3's loops `break` because their
conditions dereference `to_algebraic()` — and its debug builds then
`SASSERT(gt(upper, lower))` inside `select_small_core`, i.e. the
*contract* is "brackets cleared", which the break does not deliver.
The state is unreachable in default Z3 only because `factor=true`
makes rational-rooted cells basic at construction; we have no
factorization yet (nla-27), so the probe
`select (x²−4 cell (1,3)) (x²−9 cell (0,4))` reached the broken
dispatch and returned a non-strict witness. Recursing enforces the
SASSERT contract and is a no-op whenever the source's break was safe.
Terminates: distinct values ⇒ the halving brackets separate, and at
most two became-basic shape changes can occur. -/
partial def separate (x y : RAlg) : RAlg × RAlg :=
  match x, y with
  | .rat p, .root _ cl _ =>
    if cl.leRat p then
      match refine1 y with
      | y'@(.root _ _ _) => separate x y'
      | y' => (x, y')          -- curr became basic: rat/rat needs nothing
    else (x, y)
  | .root _ _ pu _, .rat c =>
    if pu.geRat c then
      match refine1 x with
      | x'@(.root _ _ _) => separate x' y
      | x' => (x', y)          -- prev became basic: rat/rat needs nothing
    else (x, y)
  | .root _ _ pu _, .root _ cl _ _ =>
    if Mpbq.ge pu cl then
      let x' := refine1 x
      let y' := refine1 y
      match x', y' with
      | .root _ _ _ _, .root _ _ _ _ => separate x' y'
      | _, _ => separate x' y' -- shape changed: re-dispatch (see above)
    else (x, y)
  | _, _ => (x, y)             -- basic/basic: do nothing

/-- z3 `am::select` (`algebraic_numbers.cpp:2856`), nla-26.4: a "nice"
(few-bit dyadic) value strictly between `x < y` — separate the brackets,
then `select_small_core` on the four basic/algebraic shapes: open
rational bounds on basic sides, the (cleared) bracket endpoints on
algebraic sides. This is the witness picker's gap selection, replacing
`ratBetween`. nla-28: z3's `select(numeral &, numeral &)` mutates both
sides via `separate`; we return the separated cells alongside. -/
def select (x y : RAlg) : Rat × RAlg × RAlg :=
  let (x, y) := separate x y
  let w : Mpbq :=
    match x, y with
    | .rat p, .rat c => Mpbq.selectSmallCoreQQ p c
    | .rat p, .root _ cl _ _ => Mpbq.selectSmallCoreQD p cl
    | .root _ _ pu _, .rat c => Mpbq.selectSmallCoreDQ pu c
    | .root _ _ pu _, .root _ cl _ _ => Mpbq.selectSmallCoreDD pu cl
  (w.toRat, x, y)

/-- z3 `compare_core` (`algebraic_numbers.cpp:1929`) — both arguments
algebraic. Stages, each ending in the `COMPARE_INTERVAL` disjointness
check:

1. interval disjointness (cheap path);
2. same defining polynomial + overlapping intervals ⇒ same root
   (`compare_p`; sound by the same-isolation-run invariant);
3. **minimal-polynomial branch** (nla-27): both cells minimal ⇒
   distinct polynomials ⇒ DISTINCT roots ⇒ refine-until-disjoint
   terminates. In default z3 (`factor=true`) this is the COMMON path;
   became-basic is impossible here (minimal non-linear ⇒ irrational,
   z3 SASSERT) — our `.inr` fallbacks are pure safety nets;
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
   orients the answer.

nla-28: z3's `compare_core(numeral & a, numeral & b)` refines both cells
in place (stages 3–4) and the mutation persists; we return the refined
cells alongside the verdict, including on the became-basic re-dispatch
paths (z3 `return compare(a, b)` with `a`/`b` already mutated). -/
def compareCore (p1 : QPoly) (a1 b1 : Mpbq) (m1 : Bool)
    (p2 : QPoly) (a2 b2 : Mpbq) (m2 : Bool) :
    Ordering × RAlg × RAlg := Id.run do
  -- COMPARE_INTERVAL
  if Mpbq.le b1 a2 then return (.lt, .root p1 a1 b1 m1, .root p2 a2 b2 m2)
  if Mpbq.ge a1 b2 then return (.gt, .root p1 a1 b1 m1, .root p2 a2 b2 m2)
  -- compare_p: same polynomial + overlap ⇒ same root
  if p1 == p2 then return (.eq, .root p1 a1 b1 m1, .root p2 a2 b2 m2)
  let s1 := evalSignAtD p1 a1
  let s2 := evalSignAtD p2 a2
  let mut x1 := a1; let mut y1 := b1
  let mut x2 := a2; let mut y2 := b2
  -- minimal polynomials: distinct polys ⇒ distinct roots ⇒ separate
  if m1 && m2 then
    let mut go := true
    while go do
      match refineCoreStepD p1 (evalSignAtD p1 x1) x1 y1 with
      | .inr r =>  -- safety net (z3 SASSERTs unreachable: minimal ⇒ irrational)
        return ((compareRootRat p2 x2 y2 r.toRat).swap, .rat r.toRat, .root p2 x2 y2 m2)
      | .inl (x1', y1') =>
        x1 := x1'; y1 := y1'
        match refineCoreStepD p2 (evalSignAtD p2 x2) x2 y2 with
        | .inr r =>
          return (compareRootRat p1 x1 y1 r.toRat, .root p1 x1 y1 m1, .rat r.toRat)
        | .inl (x2', y2') =>
          x2 := x2'; y2 := y2'
          if Mpbq.le y1 x2 then
            return (.lt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
          if Mpbq.ge x1 y2 then
            return (.gt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  -- magnitude equalization
  let aM := intervalMagnitude x1 y1
  let bM := intervalMagnitude x2 y2
  let targetM := max minMagnitude (min aM bM)
  if bM > targetM then
    match refineStepsD p2 s2 x2 y2 (bM - targetM).toNat with
    | .inr r => return (compareRootRat p1 x1 y1 r.toRat, .root p1 x1 y1 m1, .rat r.toRat)
    | .inl (x2', y2') =>
      x2 := x2'; y2 := y2'
      if Mpbq.le y1 x2 then return (.lt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
      if Mpbq.ge x1 y2 then return (.gt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  if aM > targetM then
    match refineStepsD p1 s1 x1 y1 (aM - targetM).toNat with
    | .inr r => return ((compareRootRat p2 x2 y2 r.toRat).swap, .rat r.toRat, .root p2 x2 y2 m2)
    | .inl (x1', y1') =>
      x1 := x1'; y1 := y1'
      if Mpbq.le y1 x2 then return (.lt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
      if Mpbq.ge x1 y2 then return (.gt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  if targetM > minMagnitude then
    for _ in [0:(targetM - minMagnitude).toNat] do
      match refineCoreStepD p1 s1 x1 y1 with
      | .inr r => return ((compareRootRat p2 x2 y2 r.toRat).swap, .rat r.toRat, .root p2 x2 y2 m2)
      | .inl (x1', y1') =>
        x1 := x1'; y1 := y1'
        match refineCoreStepD p2 s2 x2 y2 with
        | .inr r => return (compareRootRat p1 x1 y1 r.toRat, .root p1 x1 y1 m1, .rat r.toRat)
        | .inl (x2', y2') =>
          x2 := x2'; y2 := y2'
          if Mpbq.le y1 x2 then return (.lt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
          if Mpbq.ge x1 y2 then return (.gt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  -- Sturm workaround: separate refined copies (precision 10 ⇒ 40 bits)
  match refineToPrecD p1 s1 x1 y1 40, refineToPrecD p2 s2 x2 y2 40 with
  | .inl (la, ua), .inl (lb, ub) =>
    if Mpbq.gt la ub then return (.gt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
    if Mpbq.lt ua lb then return (.lt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  | _, _ => pure ()
  -- expensive case: Sturm–Tarski
  let V : Int := tarskiQuery p2 p1 x1.toRat y1.toRat
  if V == 0 then return (.eq, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  if (V < 0) == (s2 < 0) then return (.lt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)
  return (.gt, .root p1 x1 y1 m1, .root p2 x2 y2 m2)

/-- Total comparison — z3 `am::compare` dispatch
(`algebraic_numbers.cpp:2108`). Unfueled: see `compareCore`. nla-28:
returns the refined cells; the root-vs-rational dispatches never refine
(z3 `compare(algebraic_cell, mpq)` is mutation-free), so they return
their inputs unchanged. -/
def compare (x y : RAlg) : Ordering × RAlg × RAlg :=
  match x, y with
  | .rat p, .rat q => (if p < q then .lt else if p == q then .eq else .gt, .rat p, .rat q)
  | .root p a b m, .rat q => (compareRootRat p a b q, .root p a b m, .rat q)
  | .rat q, .root p a b m => ((compareRootRat p a b q).swap, .rat q, .root p a b m)
  | .root p1 a1 b1 m1, .root p2 a2 b2 m2 => compareCore p1 a1 b1 m1 p2 a2 b2 m2

def lt (x y : RAlg) : Bool × RAlg × RAlg :=
  let (o, x', y') := compare x y
  (o == .lt, x', y')

def le (x y : RAlg) : Bool × RAlg × RAlg :=
  let (o, x', y') := compare x y
  (o != .gt, x', y')

/-- Isolate all real roots of `p0` as `RAlg` values, sorted ascending —
the `am::isolate_roots` pipeline (nla-27, default `factor=true` parity):
strip zero roots (`has_zero_roots`/`remove_zero_roots`, 0 becomes a
basic root), factor the rest over ℤ (`upolynomial::factor`), linear
factors become basic rationals `−c₀/c₁` directly, and each higher-degree
factor's roots are isolated per-factor carrying THAT irreducible factor
with `minimal = full_fact` (z3 `mk_algebraic_cell(f, …, full_fact)`).
Isolation itself stays our Sturm engine (declared Sturm-vs-Descartes
divergence); the ℚ↔ℤ bridge is `QPoly.toZPoly`/`ZPoly.toQPoly`.
`full_fact = false` (search budget) ⇒ cells are built with
`minimal = false`, exactly z3's consequence. -/
def isolateRoots (p0 : QPoly) : Array RAlg := Id.run do
  if QPoly.isZero p0 then return #[]   -- ignore the zero polynomial
  let mut roots : Array RAlg := #[]
  -- strip zero roots
  let zp0 := QPoly.toZPoly p0
  let mut nz := zp0
  if ZPoly.coeff zp0 0 == 0 then
    roots := roots.push (.rat 0)
    let mut k := 0
    while k < zp0.size && ZPoly.coeff zp0 k == 0 do
      k := k + 1
    nz := ZPoly.trim (zp0.extract k zp0.size)
  -- factor over ℤ
  let (fullFact, fs) := factor nz
  for (fp, _) in fs.factors do
    if fp.size == 1 then
      pure ()   -- d == 0: constant, all roots found
    else if fp.size == 2 then
      -- linear ax + b ⇒ basic −b/a
      roots := roots.push (.rat (-(mkRat fp[0]! 1) / (mkRat fp[1]! 1)))
    else
      let fq := ZPoly.toQPoly fp
      for (a, b) in isolateRootsD fq do
        roots := roots.push (mkRoot fq a b fullFact)
  -- z3 `sort_roots` (total order on distinct values)
  return roots.qsort fun x y => ((RAlg.compare x y).1 == .lt)

end RAlg

end LeanNonlinearArith.Kernel
