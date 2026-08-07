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

/-! ## The 2-var acceptance driver's arith lemmas (design review 5, F-i)

The dump data verbatim from BOARD's F2 dump analysis (post-renameVars-
fix), goal `x0²+x1² ≥ 2 ∧ x0 ≤ 1 ∧ x1 < 1 ∧ x0 > 0 ∧ x1 > 0`. Review 5's
probe showed ALL of these close from literal-failure facts alone (no
step-fact collection): bundles 6/7 and final cores 1/3 directly, final
core 2 via one disequality trichotomy split (its `¬(x0−1=0)` fact is
invisible to linarith). -/

private def qx0 : MPoly := [(1, [(0, 1)])]
private def qx1 : MPoly := [(1, [(1, 1)])]
private def qx0sqx1sqm2 : MPoly := [(1, [(1, 2)]), (1, [(0, 2)]), (-2, [])]
private def qx0m1 : MPoly := [(1, [(0, 1)]), (-1, [])]
private def qx1m1 : MPoly := [(1, [(1, 1)]), (-1, [])]
private def qx0p1 : MPoly := [(1, [(0, 1)]), (1, [])]
private def qx0sqm2 : MPoly := [(1, [(0, 2)]), (-2, [])]

/-- Atom table verbatim from the acceptance dump: 1 `x0²+x1²<2`,
2 `x0>1`, 3 `x1<1`, 4 `x0>0`, 5 `x1>0`, 6 `x0+1>0`, 7 `x0<1`,
8 `x0=1`, 9 `x0²<2`. -/
private def drvAtoms : Array (Option Atom) :=
  #[none,
    some (.ineq ⟨.lt, [(qx0sqx1sqm2, false)]⟩),
    some (.ineq ⟨.gt, [(qx0m1, false)]⟩),
    some (.ineq ⟨.lt, [(qx1m1, false)]⟩),
    some (.ineq ⟨.gt, [(qx0, false)]⟩),
    some (.ineq ⟨.gt, [(qx1, false)]⟩),
    some (.ineq ⟨.gt, [(qx0p1, false)]⟩),
    some (.ineq ⟨.lt, [(qx0m1, false)]⟩),
    some (.ineq ⟨.eq, [(qx0m1, false)]⟩),
    some (.ineq ⟨.lt, [(qx0sqm2, false)]⟩)]

/-- Bundle 6's arith marker (core `[⟨5,false⟩,⟨1,true⟩,⟨3,false⟩]`,
proj `[⟨6,true⟩,⟨7,true⟩]`). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] [⟨6, true⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid

/-- Bundle 7's arith marker (same core, proj `[⟨8,true⟩,⟨4,true⟩,⟨9,true⟩]`
— the thomQuadratic pair on both roots of x0²−2). -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩]
        [⟨8, true⟩, ⟨4, true⟩, ⟨9, true⟩]) := by
  nlsat_arith_valid

/-- Final bundle, arith core 1: `[⟨7,true⟩,⟨9,true⟩,⟨2,true⟩]`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨7, true⟩, ⟨9, true⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- Final bundle, arith core 2: `[⟨7,true⟩,⟨8,true⟩,⟨2,true⟩]` — the
disequality case: needs one `lt_or_gt_of_ne` split of the `¬(x0−1=0)`
fact before linarith closes each branch. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨7, true⟩, ⟨8, true⟩, ⟨2, true⟩] []) := by
  nlsat_arith_valid

/-- Final bundle, arith core 3: `[⟨4,false⟩,⟨6,true⟩]`. -/
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨4, false⟩, ⟨6, true⟩] []) := by
  nlsat_arith_valid

/- Negative probe on the driver table: bundle 6 with one proj polarity
flipped is not valid and must be rejected. -/
#guard_msgs (drop error) in
example (ρ : Nat → ℝ) :
    clauseSatI (interp ρ drvAtoms)
      (arithClause [⟨5, false⟩, ⟨1, true⟩, ⟨3, false⟩] [⟨6, false⟩, ⟨7, true⟩]) := by
  nlsat_arith_valid

end LeanNonlinearArith.Nlsat.Tests.Refute
