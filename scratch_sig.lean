import LeanNonlinearArith.Nlsat.Refute
import LeanNonlinearArith.Nlsat.MPolyFactor
open LeanNonlinearArith.Nlsat
#eval MPoly.factorM [(1, [(0, 3)]), ((-6), [(0, 2)]), (11, [(0, 1)]), ((-6), [])]
#eval MPoly.factorM [(1, [(0, 2)]), (2, [(0, 1)]), (1, [])]
#eval MPoly.factorM [(1, [(0, 3)]), (3, [(0, 2)]), (3, [(0, 1)]), (1, [])]
