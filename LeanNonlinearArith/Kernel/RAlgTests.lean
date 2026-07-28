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

#guard (RAlg.compare sqrt2 sqrt3).1 == .lt
#guard (RAlg.compare sqrt3 sqrt2).1 == .gt
#guard (RAlg.compare sqrt2 phi).1 == .lt      -- √2 ≈ 1.414 < φ ≈ 1.618
#guard (RAlg.compare phi sqrt3).1 == .lt      -- φ ≈ 1.618 < √3 ≈ 1.732
#guard (RAlg.compare negSqrt2 sqrt2).1 == .lt
#guard (RAlg.compare sqrt2 sqrt2).1 == .eq
#guard (RAlg.compare sqrt2 sqrt2').1 == .eq   -- cross-representation, gcd fast path
#guard (RAlg.compare sqrt2' sqrt3).1 == .lt

/-! ## Rational endpoints of the lattice -/

#guard (RAlg.compare sqrt2 (.rat (3/2))).1 == .lt
#guard (RAlg.compare sqrt2 (.rat (7/5))).1 == .gt
#guard (RAlg.compare (.rat (3/2)) sqrt2).1 == .gt
#guard (RAlg.compare (.root #[-4, 0, 1] 1 3) (.rat 2)).1 == .eq  -- x² − 4 isolates 2
#guard (RAlg.compare (.rat 2) (.root #[-4, 0, 1] 1 3)).1 == .eq

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

-- nla-26.4: `select` = z3 am::select (separate + select_small_core).
-- Strict betweenness on every shape:
#guard
  let r := (RAlg.select sqrt2 sqrt3).1
  (RAlg.compare sqrt2 (.rat r)).1 == .lt && (RAlg.compare (.rat r) sqrt3).1 == .lt
#guard
  let r := (RAlg.select (.rat 1) sqrt2).1
  (1 : Rat) < r && (RAlg.compare (.rat r) sqrt2).1 == .lt
#guard
  let r := (RAlg.select sqrt2 (.rat (3/2))).1
  r < 3/2 && (RAlg.compare sqrt2 (.rat r)).1 == .lt
#guard
  let r := (RAlg.select sqrt2 phi).1
  (RAlg.compare sqrt2 (.rat r)).1 == .lt && (RAlg.compare (.rat r) phi).1 == .lt
-- …and the dyadic-niceness pins (smallest-denominator preference):
#guard (RAlg.select (.rat (-1)) (.rat 1)).1 == 0        -- an integer if possible
#guard (RAlg.select (.rat 0) (.rat 1)).1 == 1/2
#guard (RAlg.select sqrt2 sqrt3).1 == 3/2               -- few-bit gap witness
#guard (RAlg.select (.rat 0) sqrt2).1 == 1              -- integer bracket endpoint
-- F1 regression (2026-07-26 review): a cell that becomes basic mid-
-- separate must not leave the other bracket uncleared — this exact pair
-- returned the non-strict witness 2 before the separate re-dispatch fix
#guard
  let r := (RAlg.select (.root #[-4, 0, 1] 1 3) (.root #[-9, 0, 1] 0 4)).1
  (2 : Rat) < r && r < 3
-- mirrored shape (curr becomes basic, prev bracket uncleared)
#guard
  let r := (RAlg.select (.root #[-4, 0, 1] 0 4) (.root #[-9, 0, 1] 1 5)).1
  (2 : Rat) < r && r < 3

/-! ## isolateRoots (F5: cells always carry the square-free part) -/

-- x²−4: two root cells (no eager factoring — nla-27), values ±2
#guard
  let rs := RAlg.isolateRoots #[-4, 0, 1]
  rs.size == 2 &&
  (RAlg.compare rs[0]! (.rat (-2))).1 == .eq &&
  (RAlg.compare rs[1]! (.rat 2)).1 == .eq
-- x(x−2)(x+2): the middle root surfaces as .rat 0 via zero-straddle
#guard
  let rs := RAlg.isolateRoots #[0, -4, 0, 1]
  rs.map RAlg.sign == #[-1, 0, 1] && rs[1]! == RAlg.rat 0
-- non-square-free input: (x²−2)² isolates √2, −√2 ONCE, and cells
-- carry the square-free part (degree 2, not the degree-4 input; the
-- refinable-interval invariant would break with the original poly)
#guard
  let rs := RAlg.isolateRoots (QPoly.mul #[-2, 0, 1] #[-2, 0, 1])
  rs.size == 2 && (RAlg.compare rs[1]! sqrt2).1 == .eq &&
  (match rs[1]! with | .root p _ _ _ => p.size == 3 | _ => false)

-- intGt/intLt (z3 refine-then-ceil/floor — note ceil(upper), not ⌊·⌋+1)
#guard (RAlg.intGt sqrt2).1 == 2
#guard (RAlg.intLt sqrt2).1 == 1
#guard (RAlg.intGt (.rat 2)).1 == 3
#guard (RAlg.intLt (.rat 2)).1 == 1
#guard (RAlg.intGt negSqrt2).1 == -1
#guard (RAlg.intLt negSqrt2).1 == -2

/-! ## Unfueled compare mechanism (nla-26.3, z3 `compare_core` ladder) -/

-- heavily overlapping intervals, different polynomials — forced through
-- magnitude equalization + workaround/Sturm–Tarski
#guard (RAlg.compare (.root #[-3, 0, 1] 1 2) sqrt2').1 == .gt   -- √3 > √2
#guard (RAlg.compare sqrt2' (.root #[-3, 0, 1] 1 2)).1 == .lt
-- same value through a THIRD polynomial: (x²−2)(x−3), √2 in (1, 3/2)
#guard (RAlg.compare sqrt2 (.root #[6, -2, -3, 1] 1 (Mpbq.mk 3 1))).1 == .eq
-- rationality discovery inside the compare ladder: x²−4 in (1,3) hits 2
-- on its first refinement and re-dispatches through the rational case
#guard (RAlg.compare (.root #[-4, 0, 1] 1 3) sqrt2).1 == .gt    -- 2 > √2
#guard (RAlg.compare sqrt2 (.root #[-4, 0, 1] 1 3)).1 == .lt
-- same-polynomial fast path (identical cells)
#guard (RAlg.compare sqrt2 sqrt2).1 == .eq

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
  | .root _ a b _ => a.ltRat (3/2) && b.gtRat (7/5) && Mpbq.lt a b
  | .rat _ => false
-- endpoint signs stay opposite through refinement (the refinable invariant)
#guard
  match refine1 (refine1 sqrt2) with
  | .root p a b _ => QPoly.evalSignAtD p a * QPoly.evalSignAtD p b == -1
  | .rat _ => false

/-! ## nla-28 — is_rational port + statefulness threading -/

-- discovery, became-basic path: midpoint 2 IS the root during refinement
#guard RAlg.isRational (.root #[-4, 0, 1] 1 3) == (true, RAlg.rat 2)
-- discovery, candidate path: 1/3 is never a dyadic midpoint — found by the
-- rational-root-theorem candidate ⌊u·|aₙ|⌋/|aₙ| = ⌊(3/8)·3⌋/3
#guard RAlg.isRational (.root #[-1, 3] 0 1) == (true, RAlg.rat (1/3))
-- irrational miss: verdict false, refined cell still the same VALUE, and the
-- refinement persisted (width < 1/2 = the k = log2|aₙ|+1 = 1 precision gate)
#guard
  let (b, x') := RAlg.isRational sqrt2
  b == false && (RAlg.compare x' sqrt2).1 == .eq
#guard match (RAlg.isRational sqrt2).2 with
  | .root _ a b _ => b.toRat - a.toRat < 1/2
  | .rat _ => false
-- restore_if_too_small: |aₙ| = 65536 forces refinement to width < 2⁻¹⁷
-- (magnitude below minMagnitude = −16); on the miss the ORIGINAL interval
-- is restored — the returned cell is the input, not the over-refined one
#guard RAlg.isRational (.root #[-2, 0, 65536] 0 1)
  == (false, .root #[-2, 0, 65536] 0 1)
-- threading: intGt's refine-to-width-<1/2 persists in the returned cell
#guard match (RAlg.intGt sqrt2).2 with
  | .root _ a b _ => b.toRat - a.toRat < 1/2
  | .rat _ => false
-- threading: select's separate refines both sides; returned cells are the
-- same values (compare eq against the originals)
#guard
  let (_, x', y') := RAlg.select sqrt2 sqrt3
  (RAlg.compare x' sqrt2).1 == .eq && (RAlg.compare y' sqrt3).1 == .eq
-- threading: compare through the equalization ladder returns refined cells
-- of the same values
#guard
  let (o, x', y') := RAlg.compare sqrt2' sqrt3
  o == .lt && (RAlg.compare x' sqrt2').1 == .eq && (RAlg.compare y' sqrt3).1 == .eq

/-! ## nla-27 — factorization parity (default z3 `factor=true`) -/

-- eager rational discovery: x²−4 factors into linear factors over ℤ,
-- so BOTH roots are basic at construction (z3 `factor=true` behavior;
-- pre-nla-27 they were root-cells discovered lazily)
#guard RAlg.isolateRoots #[-4, 0, 1] == #[RAlg.rat (-2), RAlg.rat 2]
-- zero-strip + full factorization: x³−4x = x(x−2)(x+2) — all basic
#guard RAlg.isolateRoots #[0, -4, 0, 1] == #[RAlg.rat (-2), RAlg.rat 0, RAlg.rat 2]
-- irreducible factors carry minimal = true (z3 `m_minimal` from
-- `full_fact`); cells carry the irreducible factor itself
#guard
  let rs := RAlg.isolateRoots #[-2, 0, 1]
  rs.size == 2 && (match rs[0]!, rs[1]! with
    | .root p _ _ true, .root q _ _ true => p == #[-2, 0, 1] && q == #[-2, 0, 1]
    | _, _ => false)
-- compareCore minimal branch: distinct minimal polys with overlapping
-- intervals refine-until-disjoint (the COMMON path in default z3) —
-- √2 vs φ in (1,2): exactly one bisection each, then brackets clear
#guard (RAlg.compare (.root #[-2, 0, 1] 1 2 true) (.root #[-1, -1, 1] 1 2 true))
  == (.lt, .root #[-2, 0, 1] 1 (Mpbq.mk 3 1) true,
            .root #[-1, -1, 1] (Mpbq.mk 3 1) 2 true)
-- mirrored verdict through the same branch
#guard (RAlg.compare (.root #[-1, -1, 1] 1 2 true) (.root #[-2, 0, 1] 1 2 true)).1 == .gt
-- isRational short-circuits on minimal cells (z3 `m_not_rational` set
-- at construction): NO refinement is performed
#guard RAlg.isRational (.root #[-2, 0, 1] 1 2 true)
  == (false, .root #[-2, 0, 1] 1 2 true)
-- non-minimal cells of the same values skip the minimal branch but
-- agree on the verdict (behavioral consistency across paths)
#guard (RAlg.compare sqrt2 phi).1 == .lt

end LeanNonlinearArith.Kernel.RAlgTests
