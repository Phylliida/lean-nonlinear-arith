import LeanNonlinearArith.Nlsat.Solver
import LeanNonlinearArith.Nlsat.Explain

/-! Scratch: the √2-grade refutation dump (F4 acceptance target):
`x0 ≥ 0 ∧ x0² ≥ 2 ∧ x0 ≤ 1`. Atoms are sign-vs-0 (le/ge as negated
literals): x0 ≥ 0 ≡ ¬(x0<0); x0² ≥ 2 ≡ ¬((x0²−2)<0); x0 ≤ 1 ≡ ¬((x0−1)>0). -/

namespace LeanNonlinearArith.Nlsat.Dump2

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Solver

private def x0 : MPoly := MPoly.ofVar 0

def go : IO Unit := do
  let r := Solver.run' (do
    Solver.init
    let _ ← mkVar false
    let sq2 := (x0.mul x0).sub (MPoly.ofInt 2)   -- x0² − 2
    let xm1 := x0.sub (MPoly.ofInt 1)            -- x0 − 1
    let l1 ← mkIneqLiteral (IneqAtom.mk .lt [(x0, false)])    -- x0 < 0
    let l2 ← mkIneqLiteral (IneqAtom.mk .lt [(sq2, false)])   -- x0²−2 < 0
    let l3 ← mkIneqLiteral (IneqAtom.mk .gt [(xm1, false)])   -- x0−1 > 0
    let _ ← mkClause #[l1.negate] false   -- x0 ≥ 0
    let _ ← mkClause #[l2.negate] false   -- x0² ≥ 2
    let _ ← mkClause #[l3.negate] false   -- x0 ≤ 1
    let out ← Solver.check (Solver.resolve Explain.explain)
    let s ← get
    return (out, s.refutation))
  IO.println (repr r)

end LeanNonlinearArith.Nlsat.Dump2

def main : IO Unit := LeanNonlinearArith.Nlsat.Dump2.go
