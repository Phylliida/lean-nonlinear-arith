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

/-! ## Interval arithmetic -/

#guard RatInterval.pow (-2, 3) 2 == ((0 : Rat), 9)     -- even tightening
#guard RatInterval.pow (-3, -1) 2 == ((1 : Rat), 9)    -- negative range
#guard RatInterval.pow (-2, 3) 3 == ((-8 : Rat), 27)   -- odd is monotone
#guard RatInterval.mul (1, 2) (-3, 4) == ((-6 : Rat), 8)
#guard RatInterval.containsZero (-1, 1)
#guard !RatInterval.containsZero (1/8, 1)

-- x² + y over x ∈ [−1, 1], y ∈ [2, 3] ⇒ [2, 4]
private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
#guard (MPoly.add (MPoly.mul x0 x0) x1).evalInterval
  (fun v => if v == 0 then (-1, 1) else (2, 3)) == ((2 : Rat), 4)

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

#guard RAlg.intervalOf sqrt2 == ((1 : Rat), 2)
#guard RAlg.width (RAlg.rat (7/2)) == 0
#guard RAlg.width (RAlg.refineUntilWidth sqrt2 (1/1024)) < 1/1024
-- refinement keeps enclosing √2: interval evaluation of x²−2 must span 0
#guard (MPoly.sub (MPoly.mul x0 x0) (MPoly.ofRat 2)).evalInterval
  (fun _ => RAlg.intervalOf (RAlg.refineUntilWidth sqrt2 (1/1024)))
  |> RatInterval.containsZero

-- nla-26.5 rationality discovery through refine_until_prec: a root cell
-- whose midpoint hits the root exactly becomes basic
#guard RAlg.refineUntilWidth (.root #[-4, 0, 1] 1 3) (1/1024) == RAlg.rat 2

end LeanNonlinearArith.Nlsat.AnumEvalTests
