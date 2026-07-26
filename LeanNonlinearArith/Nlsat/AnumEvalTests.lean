import LeanNonlinearArith.Nlsat.AnumEval

/-!
# nla-12b-i tests — evaluator anum foundations

The `resultantElim` pins are hand-traced through the multiplication-matrix
construction (the classic eliminations: `√2` as `Res_x(y − x, x² − 2)`,
`√2·√3` by sequential elimination, non-monic scaling faithfulness).
-/

namespace LeanNonlinearArith.Nlsat.AnumEvalTests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.AnumEval

/-! ## Interval arithmetic (`MpbqI` = mpbqi, exact dyadic) -/

#guard MpbqI.pow ⟨-2, 3⟩ 2 == (⟨0, 9⟩ : MpbqI)         -- even tightening
#guard MpbqI.pow ⟨-3, -1⟩ 2 == (⟨1, 9⟩ : MpbqI)        -- negative range
#guard MpbqI.pow ⟨-2, 3⟩ 3 == (⟨-8, 27⟩ : MpbqI)       -- odd is monotone
#guard MpbqI.mul ⟨1, 2⟩ ⟨-3, 4⟩ == (⟨-6, 8⟩ : MpbqI)
#guard MpbqI.containsZero ⟨-1, 1⟩
#guard !MpbqI.containsZero ⟨Mpbq.mk 1 3, 1⟩
-- dyadic endpoints stay exact through mul/pow
#guard MpbqI.mul ⟨Mpbq.mk 1 1, Mpbq.mk 3 1⟩ ⟨Mpbq.mk 1 2, Mpbq.mk 5 2⟩
  == (⟨Mpbq.mk 1 3, Mpbq.mk 15 3⟩ : MpbqI)  -- [1/2,3/2]·[1/4,5/4] = [1/8,15/8]

-- x² + y over x ∈ [−1, 1], y ∈ [2, 3] ⇒ [2, 4]
private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
#guard (MPoly.add (MPoly.mul x0 x0) x1).evalInterval
  (fun v => if v == 0 then ⟨-1, 1⟩ else ⟨2, 3⟩) == (⟨2, 4⟩ : MpbqI)

/-! ## Resultant elimination (`q` univariate rational) -/

private def y2 : MPoly := MPoly.ofVar 2

-- Res_x(y − x, x² − 2) = y² − 2 (the minimal polynomial of √2)
#guard (resultantElim (MPoly.sub y2 x0) 0 #[-2, 0, 1]).toQPoly? 2
  == some #[-2, 0, 1]

-- Res_x(y − x², x² − 2) = (y − 2)²
#guard (resultantElim (MPoly.sub y2 (MPoly.mul x0 x0)) 0 #[-2, 0, 1]).toQPoly? 2
  == some #[4, -4, 1]

-- √6 by sequential elimination: y − x₀·x₁, then x₀ ↦ x²−2, x₁ ↦ x²−3
private def elim6 : MPoly :=
  resultantElim (resultantElim (MPoly.sub y2 (MPoly.mul x0 x1)) 0 #[-2, 0, 1])
    1 #[-3, 0, 1]
-- (y² − 6)² = y⁴ − 12y² + 36; roots ±√6
#guard elim6.toQPoly? 2 == some #[36, 0, -12, 0, 1]

-- √2 + √3 the same way: minimal polynomial x⁴ − 10x² + 1 appears squared
private def elimSum : MPoly :=
  resultantElim (resultantElim (MPoly.sub y2 (MPoly.add x0 x1)) 0 #[-2, 0, 1])
    1 #[-3, 0, 1]
#guard elimSum.toQPoly? 2 == some #[1, 0, -10, 0, 1]

-- non-monic q keeps the faithful lc scalar: Res_x(y − x, 2x² − 4) = 2y² − 4
#guard (resultantElim (MPoly.sub y2 x0) 0 #[-4, 0, 2]).toQPoly? 2
  == some #[-4, 0, 2]

-- constant-in-x f: Res_x(y, x² − 2) = y²
#guard (resultantElim y2 0 #[-2, 0, 1]).toQPoly? 2 == some #[0, 0, 1]

/-! ## Nonzero-root lower bound -/

private def checkBound (p : QPoly) (root : Rat) : Bool :=
  -- the bound must be valid for a known smallest-magnitude nonzero root
  let k := nonzeroRootLowerBound p
  ((1 : Rat) / (2 ^ k)) < (if root < 0 then -root else root)

#guard checkBound #[-1/4, 0, 1] (1/2)     -- x² − ¼, roots ±½
#guard checkBound #[0, -2, 0, 1] (-1414/1000)  -- x³ − 2x: nonzero roots ±√2 (bound vs ≈1.414 underestimate is safe: bound < √2 required)
#guard nonzeroRootLowerBound #[0, 0, 1] == 0   -- x²: no nonzero roots
#guard nonzeroRootLowerBound #[] == 0
#guard nonzeroRootLowerBound #[5] == 0

/-! ## RAlg accessors -/

private def sqrt2 : RAlg := .root #[-2, 0, 1] 1 2

#guard RAlg.intervalD sqrt2 == some ⟨1, 2⟩
#guard RAlg.intervalD (RAlg.rat (7/2)) == none  -- basic values never enter
#guard RAlg.width (RAlg.rat (7/2)) == 0
#guard RAlg.width (RAlg.refineUntilPrec sqrt2 10) < 1/1024
-- refinement keeps enclosing √2: interval evaluation of x²−2 must span 0
#guard (MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 2)).evalInterval
  (fun _ => (RAlg.intervalD (RAlg.refineUntilPrec sqrt2 10)).getD ⟨0, 0⟩)
  |> MpbqI.containsZero

-- nla-26.5 rationality discovery through refine_until_prec: a root cell
-- whose midpoint hits the root exactly becomes basic
#guard RAlg.refineUntilPrec (.root #[-4, 0, 1] 1 3) 10 == RAlg.rat 2

end LeanNonlinearArith.Nlsat.AnumEvalTests
