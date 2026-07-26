import LeanNonlinearArith.Kernel.RAlg

/-!
# RAlg tests — mini-anum behavior pins

`#guard` (native evaluation) — untrusted kernel behavior, pinned against
hand-checked algebraic facts.
-/

namespace LeanNonlinearArith.Kernel.RAlgTests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Kernel.RAlg

/-- √2 as the root of x² − 2 in (1, 2). -/
def sqrt2 : RAlg := .root #[-2, 0, 1] 1 2
/-- √2 again, as the only root of (x² − 2)(x² − 3) in (1, 13/8)
(dyadic upper endpoint between √2 ≈ 1.414 and √3 ≈ 1.732). -/
def sqrt2' : RAlg := .root #[6, 0, -5, 0, 1] 1 (Mpbq.mk 13 3)
/-- √3. -/
def sqrt3 : RAlg := .root #[-3, 0, 1] 1 2
/-- Golden ratio φ ≈ 1.618, root of x² − x − 1 in (1, 2). -/
def phi : RAlg := .root #[-1, -1, 1] 1 2
/-- −√2. -/
def negSqrt2 : RAlg := .root #[-2, 0, 1] (-2) (-1)

/-! ## Comparisons -/

#guard RAlg.compare sqrt2 sqrt3 == .lt
#guard RAlg.compare sqrt3 sqrt2 == .gt
#guard RAlg.compare sqrt2 phi == .lt      -- √2 ≈ 1.414 < φ ≈ 1.618
#guard RAlg.compare phi sqrt3 == .lt      -- φ ≈ 1.618 < √3 ≈ 1.732
#guard RAlg.compare negSqrt2 sqrt2 == .lt
#guard RAlg.compare sqrt2 sqrt2 == .eq
#guard RAlg.compare sqrt2 sqrt2' == .eq   -- cross-representation, gcd fast path
#guard RAlg.compare sqrt2' sqrt3 == .lt

/-! ## Rational endpoints of the lattice -/

#guard RAlg.compare sqrt2 (.rat (3/2)) == .lt
#guard RAlg.compare sqrt2 (.rat (7/5)) == .gt
#guard RAlg.compare (.rat (3/2)) sqrt2 == .gt
#guard RAlg.compare (.root #[-4, 0, 1] 1 3) (.rat 2) == .eq  -- x² − 4 isolates 2
#guard RAlg.compare (.rat 2) (.root #[-4, 0, 1] 1 3) == .eq

/-! ## mkRoot normalization (linear ⇒ rational) -/

#guard mkRoot #[0, 1] (-1) 1 == RAlg.rat 0        -- x ⇒ 0
#guard mkRoot #[-6, 2] 2 4 == RAlg.rat 3          -- 2x − 6 ⇒ 3
#guard mkRoot #[-2, 0, 1] 1 2 == sqrt2            -- quadratic kept as root

/-! ## Signs -/

#guard sign sqrt2 == 1
#guard sign negSqrt2 == -1
#guard sign (RAlg.rat 0) == 0
#guard sign (RAlg.rat (-3/7)) == -1

#guard signOfPolyAt #[-3, 0, 1] sqrt2 == -1   -- (√2)² − 3 < 0
#guard signOfPolyAt #[-1, 0, 1] sqrt2 == 1    -- (√2)² − 1 > 0
#guard signOfPolyAt #[-2, 0, 1] sqrt2 == 0    -- (√2)² − 2 = 0
#guard signOfPolyAt #[-1, -1, 1] sqrt2 == -1  -- √2 below φ's poly's root
#guard signOfPolyAt #[0, 1] negSqrt2 == -1    -- identity poly: sign of −√2

/-! ## Rational separation (witness picking) -/

#guard (ratBetween sqrt2 sqrt3).any fun r =>
  RAlg.compare sqrt2 (.rat r) == .lt && RAlg.compare (.rat r) sqrt3 == .lt
#guard (ratBetween (.rat 1) sqrt2).any fun r =>
  (1 : Rat) < r && RAlg.compare (.rat r) sqrt2 == .lt
#guard (ratBetween sqrt2 (.rat (3/2))).any fun r =>
  r < 3/2 && RAlg.compare sqrt2 (.rat r) == .lt
#guard (ratBetween sqrt2 phi).any fun r =>
  RAlg.compare sqrt2 (.rat r) == .lt && RAlg.compare (.rat r) phi == .lt
#guard (ratBetween (.rat (-1)) (.rat 1)).any fun r => r == 0

/-! ## Unfueled compare mechanism (nla-26.3, z3 `compare_core` ladder) -/

-- heavily overlapping intervals, different polynomials — forced through
-- magnitude equalization + workaround/Sturm–Tarski
#guard RAlg.compare (.root #[-3, 0, 1] 1 2) sqrt2' == .gt   -- √3 > √2
#guard RAlg.compare sqrt2' (.root #[-3, 0, 1] 1 2) == .lt
-- same value through a THIRD polynomial: (x²−2)(x−3), √2 in (1, 3/2)
#guard RAlg.compare sqrt2 (.root #[6, -2, -3, 1] 1 (Mpbq.mk 3 1)) == .eq
-- rationality discovery inside the compare ladder: x²−4 in (1,3) hits 2
-- on its first refinement and re-dispatches through the rational case
#guard RAlg.compare (.root #[-4, 0, 1] 1 3) sqrt2 == .gt    -- 2 > √2
#guard RAlg.compare sqrt2 (.root #[-4, 0, 1] 1 3) == .lt
-- same-polynomial fast path (identical cells)
#guard RAlg.compare sqrt2 sqrt2 == .eq

/-! ## mkRoot normalization (nla-26.3, z3 `am::normalize`):
zero never strictly inside an isolating interval -/

-- ∛2 in (−1, 2): p and p(0) share sign ⇒ lower snaps to 0
#guard mkRoot #[-2, 0, 0, 1] (-1) 2
  == RAlg.root #[-2, 0, 0, 1] (Mpbq.ofInt 0) (Mpbq.ofInt 2)
-- −∛2 in (−2, 1): signs differ ⇒ upper snaps to 0
#guard mkRoot #[2, 0, 0, 1] (-2) 1
  == RAlg.root #[2, 0, 0, 1] (Mpbq.ofInt (-2)) (Mpbq.ofInt 0)
-- x(x−2)(x+2) isolating 0 in (−1, 1): the value IS zero ⇒ basic
#guard mkRoot #[0, -4, 0, 1] (-1) 1 == RAlg.rat 0
-- non-straddling intervals pass through untouched
#guard mkRoot #[-2, 0, 1] 1 2 == sqrt2

/-! ## Refinement + rationality discovery (nla-26.5, z3 `am::refine`) -/

-- x² − 4 isolating 2 in (1, 3): the very first midpoint IS the root —
-- the cell becomes basic (the divergence this port eliminates: the old
-- nonRootSplit-based step dodged root midpoints forever)
#guard refine1 (.root #[-4, 0, 1] 1 3) == RAlg.rat 2
-- √2 in (1, 2): midpoint 3/2 has p > 0 = sign at b ⇒ (1, 3/2) survives
#guard refine1 sqrt2 == RAlg.root #[-2, 0, 1] 1 (Mpbq.mk 3 1)
-- iterated refinement stays a root cell and keeps bracketing √2
#guard
  let x := refine1 (refine1 (refine1 sqrt2))
  match x with
  | .root _ a b => a.ltRat (3/2) && b.gtRat (7/5) && Mpbq.lt a b
  | .rat _ => false
-- endpoint signs stay opposite through refinement (the refinable invariant)
#guard
  match refine1 (refine1 sqrt2) with
  | .root p a b => QPoly.evalSignAtD p a * QPoly.evalSignAtD p b == -1
  | .rat _ => false

end LeanNonlinearArith.Kernel.RAlgTests
