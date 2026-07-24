import Mathlib

/-!
# Root-counting spike (nla-02)

Tests whether mathlib-today supports the per-instance certified root counting
the trace checker needs (S2-lite), without formalizing general Sturm theory:

* sign invariance from rootlessness (IVT contrapositive) — the workhorse for
  "q has constant sign on the cell, so its sign at the sample decides it";
* existence from a sign change (IVT) and uniqueness from strict monotonicity
  (derivative positivity) — root isolation for a concrete polynomial;
* the global Rolle-chain bound `Polynomial.card_roots_le_derivative` composing
  with the above for exact counts.

Findings feed the nla-02 board item; if this pattern scales to census
specimens, general Sturm (nla-10) may be avoidable for the checker.
-/

open Set Polynomial

namespace LeanNonlinearArith

/-- **Sign invariance from rootlessness.** A function continuous on `[a,b]`
with no zero there has the same sign at any two points. This discharges the
"constant sign on the cell" obligations in nlsat traces. -/
theorem sign_invariant_of_no_root {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) (h0 : ∀ x ∈ Icc a b, f x ≠ 0) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, (0 < f x ↔ 0 < f y) := by
  have key : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, 0 < f x → 0 < f y := by
    intro x hx y hy hfx
    by_contra hfy
    have hfy' : f y < 0 := lt_of_le_of_ne (not_lt.mp hfy) (h0 y hy)
    have hsub : uIcc x y ⊆ Icc a b := (Set.ordConnected_Icc).uIcc_subset hx hy
    have hmem : (0 : ℝ) ∈ uIcc (f x) (f y) := by
      rw [mem_uIcc]; right; exact ⟨hfy'.le, hfx.le⟩
    obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc (hf.mono hsub) hmem
    exact h0 z (hsub hz) hz0
  exact fun x hx y hy => ⟨key x hx y hy, key y hy x hx⟩

/-- Concrete isolation instance: `x² - 2` has exactly one root in `[1, 2]`. -/
theorem sq_sub_two_unique_root : ∃! x, x ∈ Icc (1:ℝ) 2 ∧ x ^ 2 - 2 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2 - 2) (Icc 1 2) := by fun_prop
  -- existence: sign change on [1,2]
  have hex : ∃ x ∈ Icc (1:ℝ) 2, x ^ 2 - 2 = 0 := by
    have h : (0:ℝ) ∈ Icc ((1:ℝ) ^ 2 - 2) ((2:ℝ) ^ 2 - 2) := by norm_num
    obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc (by norm_num : (1:ℝ) ≤ 2) hcont h
    exact ⟨z, hz, hz0⟩
  -- uniqueness: strictly monotone on [1,2] since the derivative 2x is positive
  have hmono : StrictMonoOn (fun x : ℝ => x ^ 2 - 2) (Icc 1 2) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 1 2) hcont
    intro x hx
    rw [interior_Icc] at hx
    have : deriv (fun x : ℝ => x ^ 2 - 2) x = 2 * x := by
      simp [differentiableAt_fun_id]
    rw [this]
    linarith [hx.1]
  obtain ⟨z, hz, hz0⟩ := hex
  refine ⟨z, ⟨hz, hz0⟩, ?_⟩
  rintro y ⟨hy, hy0⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h2 := hmono hy hz h; simp only at h2; linarith
  · have h2 := hmono hz hy h; simp only at h2; linarith

/-- The Rolle-chain bound composes: `X² - 2` has at most 2 distinct real roots,
by one step of `card_roots_toFinset_le_derivative`. (Global bound; interval
localization comes from intersecting with isolation intervals as above.) -/
theorem sq_sub_two_card_roots_le :
    ((X ^ 2 - C 2 : ℝ[X]).roots.toFinset.card) ≤ 2 := by
  have h := Polynomial.card_roots_toFinset_le_derivative (X ^ 2 - C 2 : ℝ[X])
  have hderiv : Polynomial.derivative (X ^ 2 - C 2 : ℝ[X]) = C 2 * X := by
    simp [Polynomial.derivative_sub, Polynomial.derivative_pow]
  rw [hderiv] at h
  have : ((C 2 * X : ℝ[X]).roots.toFinset.card) ≤ 1 := by
    have h2 : (C 2 * X : ℝ[X]).roots = (X : ℝ[X]).roots := by
      rw [Polynomial.roots_C_mul _ (by norm_num : (2:ℝ) ≠ 0)]
    rw [h2, Polynomial.roots_X]
    simp
  omega

end LeanNonlinearArith
