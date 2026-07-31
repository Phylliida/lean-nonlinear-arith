import LeanNonlinearArith.Kernel.BivPoly

/-!
# nla-29.1c tests — bivariate composition + resultant elimination pins

Hand-checked values for the `mk_binary` polynomial shapes. The headline
pins are the classical eliminations, cross-checked against the
independent `AnumEval` route's pins (√2+√3 ↦ x⁴−10x²+1 lives in
`Nlsat/AnumEvalTests.lean` via `substRat`-style substitution; agreement
across the two routes is the differential).
-/

namespace LeanNonlinearArith.Kernel.BivPoly.Tests

open LeanNonlinearArith.Kernel.QPoly

private def p (cs : Array Rat) : QPoly := QPoly.trim cs

private def x2m2 : QPoly := p #[-2, 0, 1]          -- x²−2
private def y2m3 : QPoly := p #[-3, 0, 1]          -- y²−3

-- ## arithmetic + composition shapes
-- (x−y)² = x² − 2xy + y²
#guard BivPoly.mul BivPoly.xMinusY BivPoly.xMinusY
  == #[p #[0, 0, 1], p #[0, -2], p #[1]]
-- x²−2 at (x−y): (x−y)²−2 = (x²−2) − 2xy + y²
#guard BivPoly.composeXMinusY x2m2
  == #[p #[-2, 0, 1], p #[0, -2], p #[1]]
-- x²−2 at (x+y)
#guard BivPoly.composeXPlusY x2m2
  == #[p #[-2, 0, 1], p #[0, 2], p #[1]]
-- y²·pa(x/y) for pa = x²−2: x² − 2y² (zero y¹ coefficient is the empty QPoly)
#guard BivPoly.composeXDivY x2m2
  == #[p #[0, 0, 1], #[], p #[-2]]
-- linear pa: (x−2) at (x−y) = (x−2) − y
#guard BivPoly.composeXMinusY (p #[-2, 1])
  == #[p #[-2, 1], p #[-1]]

-- ## resultantElimY (the mk_binary resultant shape)
-- √2+√3: Res_y((x−y)²−2, y²−3) = x⁴−10x²+1 (differential vs AnumEval pin)
#guard BivPoly.resultantElimY (BivPoly.composeXMinusY x2m2) y2m3
  == p #[1, 0, -10, 0, 1]
-- same through compose_x_plus_y (pb is even)
#guard BivPoly.resultantElimY (BivPoly.composeXPlusY x2m2) y2m3
  == p #[1, 0, -10, 0, 1]
-- √2·√3: Res_y(x²−2y², y²−3) = (x²−6)² = x⁴−12x²+36 — the PRODUCT
-- resultant is the square; mk_binary's factor+Sturm selection (nla-29.2)
-- is what picks out the x²−6 factor
#guard BivPoly.resultantElimY (BivPoly.composeXDivY x2m2) y2m3
  == p #[36, 0, -12, 0, 1]
-- non-monic pb: Res_y((x−y)²−2, 2y²−3) = lc(pb)²·∏f(β) = 4x⁴−28x²+1
#guard BivPoly.resultantElimY (BivPoly.composeXMinusY x2m2) (p #[-3, 0, 2])
  == p #[1, 0, -28, 0, 4]
-- linear pa: Res_y((x−2)−y, y²−3) = (x−2)²−3 = x²−4x+1
#guard BivPoly.resultantElimY (BivPoly.composeXMinusY (p #[-2, 1])) y2m3
  == p #[1, -4, 1]
-- root-content semantics: the sum/product resultants vanish at the right
-- algebraic points — checked rationally where possible: √2·√2 = 2 is a
-- root of the product resultant Res_y(x²−2y², y²−2) = (x²−4)²
#guard BivPoly.resultantElimY (BivPoly.composeXDivY x2m2) x2m2
  == p #[16, 0, -8, 0, 1]

end LeanNonlinearArith.Kernel.BivPoly.Tests
