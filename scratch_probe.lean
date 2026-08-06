import LeanNonlinearArith.Nlsat.Refute

open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

namespace ScratchProbe

private def x0 : MPoly := MPoly.ofVar 0

#eval ((x0.mul x0).sub (MPoly.ofInt 2) : MPoly)
#eval (MPoly.add [(1, [(0, 2)])] [(-2, [])] : MPoly)
#eval (Monomial.cmp [(0, 2)] [] : Ordering)
#eval (Monomial.cmp [] [(0, 2)] : Ordering)

end ScratchProbe
