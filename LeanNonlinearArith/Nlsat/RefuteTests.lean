import LeanNonlinearArith.Nlsat.Refute

/-!
# nla-19a F2 skeleton tests — the x0²+x1²<0 refutation's arith lemmas

The snapshot data is the live dump reproduced through the F2 seam
(`Solver.run'` on the unit clause `x0²+x1² < 0`; the dump is recorded
in BOARD's F2-groundwork block). Atom table:

  0: none (true bvar)   1: `x0²+x1² < 0`   2: `x0 = 0`   3: `x0 > 0`   4: `x0 < 0`

One test per `.arith` marker of the refutation (bundles 2, 3, 4, final)
plus a negative probe (an invalid clause must be rejected).
-/

namespace LeanNonlinearArith.Nlsat.Tests.Refute

open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

/- NOTE (kernel-reduction trap, pinned in BOARD): `Monomial.cmp`/
`Monomial.mul`/`MPoly.add`/`MPoly.mul` are well-founded-compiled and
do NOT reduce under kernel whnf/rfl/decide. The atom table is therefore
written in literal-list form (the same form the nla-14 tactic will
quote from the native snapshot) — never via `MPoly` ops on consts. -/
private def x0 : MPoly := [(1, [(0, 1)])]
private def x1 : MPoly := [(1, [(1, 1)])]
private def p01 : MPoly := [(1, [(1, 2)]), (1, [(0, 2)])]

private def dumpAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.lt, [(p01, false)]⟩),
    some (.ineq ⟨.eq, [(x0, false)]⟩),
    some (.ineq ⟨.gt, [(x0, false)]⟩),
    some (.ineq ⟨.lt, [(x0, false)]⟩)]

/-- Bundle 2's arith marker (core `x0²+x1²<0`, proj `¬(x0=0)`):
`¬(x0=0) ∨ ¬(x0²+x1²<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨2, true⟩]) := by
  nlsat_arith_valid

/-- Bundle 3's arith marker (proj `x0 > 0`):
`(x0>0) ∨ ¬(x0²+x1²<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨3, false⟩]) := by
  nlsat_arith_valid

/-- Bundle 4's arith marker (proj `x0 < 0`):
`(x0<0) ∨ ¬(x0²+x1²<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨4, false⟩]) := by
  nlsat_arith_valid

/-- The final bundle's arith marker (leafNumeric glue):
`¬(x0>0) ∨ ¬(x0<0)`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨3, false⟩, ⟨4, false⟩] []) := by
  nlsat_arith_valid

/- Negative probe: `(x0=0) ∨ ¬(x0²+x1²<0)` is NOT valid (ρ 0 = 1,
ρ 1 = 2 falsifies both), so the elaborator must reject. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ dumpAtoms)
      (arithClause [⟨1, false⟩] [⟨2, false⟩]) := by
  nlsat_arith_valid

end LeanNonlinearArith.Nlsat.Tests.Refute
