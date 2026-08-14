import LeanNonlinearArith.Tactic.NonlinearArith

/-!
# nla-14 Slice 2 pins — the reify+Tseitin+bridge frontend

Each `nla_frontend` example reduces the goal to the refutation goal
`∀ ρ, (integrality hyps) → (∀ C ∈ Cs, clauseHolds ρ atoms C) → False`
and then closes it BY HAND — the kernel checks the full bridge chain
(dispatch, per-literal alignment chains, NNF Iffs, proxy boundaries).
-/

namespace LeanNonlinearArith.Nlsat.Tests.Frontend

open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

/-- sq in user syntax: `x² + y² < 0` over ℝ. The frontend's table:
slot 0 = the true-bvar, atom 1 = `x*x + y*y − 2`?? — no: `lt` on
`x*x + y*y < 0` is the difference `x*x + y*y − 0` = the sum. -/
example (x y : ℝ) (h : x * x + y * y < 0) : False := by
  nla_frontend
  intro ρ hC
  have h1 := hC [⟨1, false⟩] (by native_decide)
  simp [clauseHolds, litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt]
    at h1
  -- h1 : evalP ρ p < 0 with p the sum poly — contradict nonnegativity
  have hnn : 0 ≤ evalP ρ [(1, [(1, 2)]), (1, [(0, 2)])] := by
    simp [evalP, evalM]
    positivity
  linarith

/-- The disjunctive path: a two-literal clause from `∨` in the hyps. -/
example (x y : ℝ) (h : x * x < 0 ∨ y * y < 0) : False := by
  nla_frontend
  intro ρ hC
  have h1 := hC [⟨1, false⟩, ⟨2, false⟩] (by native_decide)
  simp [clauseHolds] at h1
  rcases h1 with h1 | h1
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(0, 2)])] := by simp [evalP, evalM]; positivity
    linarith
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(1, 2)])] := by simp [evalP, evalM]; positivity
    linarith

/-- The integrality-hyp path: an Int goal emits `∃ n : ℤ, ρ x = ↑n`
before the clause hypothesis (12e decision 1 convention). -/
example (x : ℤ) (h : x * x < 0) : False := by
  nla_frontend
  intro ρ hInt hC
  obtain ⟨n, hn⟩ := hInt
  have h1 := hC [⟨1, false⟩] (by native_decide)
  simp [clauseHolds, litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt]
    at h1
  have hnn : 0 ≤ evalP ρ [(1, [(0, 2)])] := by simp [evalP, evalM]; positivity
  linarith

/-- The proxy path: an `∧` UNDER `∨` forces a Tseitin proxy — the root
clause is `[p, sqLit]` (p = bvar 3 ⇔ x≥1 ∧ x<1 over the shared lt-atom
bvar 1; sqLit = bvar 2) and the definitional clauses re-prove the
proxy's meaning via `taut_sound`. -/
example (x : ℝ) (h : (x ≥ 1 ∧ x < 1) ∨ x * x < 0) : False := by
  nla_frontend
  intro ρ hC
  have hRoot := hC [⟨3, false⟩, ⟨2, false⟩] (by native_decide)
  simp [clauseHolds, litHolds, ALitHolds, boolDefHolds, Check.Atom.Holds,
    holds_single_lt, holds_single_gt, evalP, evalM, oddProd] at hRoot
  rcases hRoot with hLeft | hSq
  · obtain ⟨hnn, hlt⟩ := hLeft
    exact absurd hlt (not_lt.mpr hnn)
  · have hnn : 0 ≤ ρ 0 ^ 2 := sq_nonneg _
    linarith

/-- The negated-goal Not-Not path: the frontend reifies `¬¬X` to X's
clause set (a two-literal clause over the two square atoms). -/
example (x y : ℝ) : ¬ (x * x < 0 ∨ y * y < 0) := by
  nla_frontend
  intro ρ hC
  have h1 := hC [⟨1, false⟩, ⟨2, false⟩] (by native_decide)
  simp [clauseHolds] at h1
  rcases h1 with h1 | h1
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(0, 2)])] := by simp [evalP, evalM]; positivity
    linarith
  · simp [litHolds, ALitHolds, Check.Atom.Holds, holds_single_lt] at h1
    have hnn : 0 ≤ evalP ρ [(1, [(1, 2)])] := by simp [evalP, evalM]; positivity
    linarith

/- div/mod never reach L2 (the L1-owned invariant): hard fail. The
error-surface pin (`#guard_msgs (error) in example …`) lands with the
Slice-4 error-reporting work. -/

end LeanNonlinearArith.Nlsat.Tests.Frontend
