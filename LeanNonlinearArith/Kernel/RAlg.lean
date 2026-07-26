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
`(a, b)` with non-root **dyadic** endpoints (nla-26.1b: Z3 keeps
isolating intervals in `mpbq` binary rationals; `isolateRootsD` emits
exactly this shape). `mkRoot` normalizes degree-1 defining polynomials to
rationals (Z3's rational fast path; `pick_in_complement` prefers rational
witnesses, so keeping rationals syntactic matters for trace parity).

Comparison strategy (`compare`): interval disjointness decides instantly;
on overlap, a common root of `gcd(p₁, p₂)` inside both open intervals
decides equality (each poly has a *unique* root in its interval, so a
shared root in the overlap identifies both); otherwise the numbers are
distinct and fueled refinement separates the intervals.
-/

namespace LeanNonlinearArith.Kernel

open QPoly

/-- Real algebraic number (kernel representation). Invariants for
`root p a b` (maintained by constructors, relied on by everything):
`p` square-free with exactly one real root in `(a, b)`, `a < b`, and
`eval p a ≠ 0 ≠ eval p b`. Endpoints are dyadic (z3 `mpbq`). -/
inductive RAlg
  | rat (q : Rat)
  | root (p : QPoly) (a b : Mpbq)
deriving Repr, Inhabited, BEq

namespace RAlg

/-- Roots of the (square-free) chain's polynomial in `(x, y]`, via Sturm.
`signVarAt` is non-increasing, so `Nat` subtraction is exact. -/
private def cnt (ch : Array QPoly) (x y : Rat) : Nat :=
  signVarAt ch x - signVarAt ch y

/-- Smart constructor: normalize linear defining polynomials to their
rational root; otherwise keep the `(poly, interval)` pair as given.
Revisited for nla-26.5: this IS Z3's shape — eager rational discovery
happens only through factorization into degree-1 factors (which we don't
port; declared), while rational roots of non-minimal higher-degree
polynomials are discovered *lazily* by `refine1`'s midpoint-zero test,
exactly as in `am::refine`. -/
def mkRoot (p : QPoly) (a b : Mpbq) : RAlg :=
  if p.size == 2 then
    -- c₀ + c₁·x ⇒ root = −c₀/c₁
    .rat (-(p.coeff 0) / p.coeff 1)
  else
    .root p a b

/-- Position of a rational `q` relative to an isolated root: `.lt` if the
root is `< q`… returned as the *root's* ordering versus `q`. -/
def compareRootRat (p : QPoly) (a b : Mpbq) (q : Rat) : Ordering :=
  if b.leRat q then .lt          -- α < b ≤ q
  else if a.geRat q then .gt     -- q ≤ a < α
  else if eval p q == 0 then .eq   -- q ∈ (a, b) and a root ⇒ q is THE root
  else
    -- q ∈ (a, b), not a root: α ∈ (a, q) or (q, b)?
    let ch := sturmChain p
    if cnt ch a.toRat q == 1 then .lt else .gt

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

/-- Compare two algebraic numbers. Fueled: each round refines both
intervals once; distinct numbers separate at depth logarithmic in their
gap. `none` on fuel exhaustion (callers treat as "give up on this
candidate" — kernel-side only). -/
def compareCore (x y : RAlg) (fuel : Nat := 128) : Option Ordering :=
  match x, y with
  | .rat p, .rat q => some (if p < q then .lt else if p == q then .eq else .gt)
  | .root p a b, .rat q => some (compareRootRat p a b q)
  | .rat q, .root p a b => some (compareRootRat p a b q).swap
  | .root p1 a1 b1, .root p2 a2 b2 => Id.run do
    -- equality test once, on the initial overlap: a common root of
    -- gcd(p₁, p₂) lying in both open intervals identifies both roots
    let g := squarefreePart (gcd p1 p2)
    if !g.isEmpty && g.size > 1 then
      let lo := Mpbq.max a1 a2
      let hi := Mpbq.min b1 b2
      if Mpbq.lt lo hi then
        -- guard endpoints: count on (lo, hi] then discount a root at hi;
        -- a root at lo is outside the open overlap
        let chg := sturmChain g
        let inOpen : Nat :=
          cnt chg lo.toRat hi.toRat - (if eval g hi.toRat == 0 then 1 else 0)
        if inOpen ≥ 1 then
          -- γ ∈ (lo, hi) ⊆ both open intervals, root of both ⇒ α₁ = γ = α₂
          return some .eq
    -- distinct: refine until the intervals separate
    let mut x1 := a1
    let mut y1 := b1
    let mut x2 := a2
    let mut y2 := b2
    for _ in [0:fuel] do
      if Mpbq.le y1 x2 then return some .lt
      if Mpbq.le y2 x1 then return some .gt
      let (x1', y1') := refineIntervalD p1 x1 y1 1
      x1 := x1'; y1 := y1'
      let (x2', y2') := refineIntervalD p2 x2 y2 1
      x2 := x2'; y2 := y2'
    return none

/-- Total comparison. The `.eq` default on fuel exhaustion is principled,
not arbitrary: distinct numbers separate within the fuel bound (128
halvings), so exhaustion happens only when refinement never separates —
i.e. when the numbers are equal but the `gcd` fast test missed an
endpoint-root edge case. Tests pin the real cases. -/
def compare (x y : RAlg) : Ordering :=
  (compareCore x y).getD .eq

def lt (x y : RAlg) : Bool := compare x y == .lt
def le (x y : RAlg) : Bool := compare x y != .gt

/-- A rational strictly between `x < y` (fueled refinement; `none` only
on fuel exhaustion or if the inputs are not actually ordered). The
witness picker's workhorse: complements of infeasible sets get rational
sample points whenever a gap is genuinely open. Returned witnesses are
values of dyadic endpoints. -/
def ratBetween (x y : RAlg) (fuel : Nat := 128) : Option Rat :=
  match x, y with
  | .rat p, .rat q => if p < q then some ((p + q) / 2) else none
  | .rat q, .root p a b => Id.run do
    -- need q < r < α: refine until the lower bracket clears q
    let mut lo := a
    let mut hi := b
    for _ in [0:fuel] do
      if lo.gtRat q then return some lo.toRat -- q < lo < α (lo non-root ⇒ lo ≠ α)
      let (lo', hi') := refineIntervalD p lo hi 1
      lo := lo'; hi := hi'
    return none
  | .root p a b, .rat q => Id.run do
    let mut lo := a
    let mut hi := b
    for _ in [0:fuel] do
      if hi.ltRat q then return some hi.toRat -- α < hi < q
      let (lo', hi') := refineIntervalD p lo hi 1
      lo := lo'; hi := hi'
    return none
  | .root p1 a1 b1, .root p2 a2 b2 => Id.run do
    let mut y1 := b1
    let mut x1 := a1
    let mut x2 := a2
    let mut y2 := b2
    for _ in [0:fuel] do
      if Mpbq.le y1 x2 then
        -- α₁ < y₁ ≤ x₂ < α₂: y₁ works unless it IS α₂'s endpoint case:
        -- y₁ ≤ x₂ < α₂ and α₁ < y₁, both strict ⇒ fine
        return some y1.toRat
      let (x1', y1') := refineIntervalD p1 x1 y1 1
      x1 := x1'; y1 := y1'
      let (x2', y2') := refineIntervalD p2 x2 y2 1
      x2 := x2'; y2 := y2'
    return none

end RAlg

end LeanNonlinearArith.Kernel
