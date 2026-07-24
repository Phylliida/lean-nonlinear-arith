import Mathlib

/-!
# Templates: division lemmas (RULES.md rows D1–D5) and monomial power bounds
(rows MB3–MB5).

D1–D3 are real-division monotonicity (likely Verus-unreachable, ported for
completeness); D4–D5 are the `Int.ediv` bounds actually reachable from
Euclidean div/mod. MB3–5 are the power/root range rules from
`monomial_bounds.cpp`.
-/

namespace LeanNonlinearArith.Templates.Divisions

/-! ## D1–D3 — real division monotonicity -/

theorem div_le_div_of_le_of_pos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x₁ x₂ y₁ y₂ : K) (hy : 0 < y₂) (hyy : y₂ ≤ y₁)
    (hx0 : 0 ≤ x₁) (hx : x₁ ≤ x₂) : x₁ / y₁ ≤ x₂ / y₂ := by
  have hy1 : 0 < y₁ := hy.trans_le hyy
  rw [div_le_div_iff₀ hy1 hy]
  nlinarith

theorem div_le_div_of_neg_of_nonneg {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x₁ x₂ y₁ y₂ : K) (hy : y₁ < 0) (hyy : y₂ ≤ y₁)
    (hx0 : 0 ≤ x₂) (hx : x₂ ≤ x₁) : x₁ / y₁ ≤ x₂ / y₂ := by
  have hy2 : y₂ < 0 := hyy.trans_lt hy
  rw [← neg_div_neg_eq x₁ y₁, ← neg_div_neg_eq x₂ y₂,
      div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem div_ge_div_of_neg_of_nonpos {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (x₁ x₂ y₁ y₂ : K) (hy : y₁ < 0) (hyy : y₂ ≤ y₁)
    (hx0 : x₂ ≤ 0) (hx : x₁ ≤ x₂) : x₂ / y₂ ≤ x₁ / y₁ := by
  have hy2 : y₂ < 0 := hyy.trans_lt hy
  rw [← neg_div_neg_eq x₂ y₂, ← neg_div_neg_eq x₁ y₁,
      div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-! ## D4–D5 — integer division bounds (`Int.ediv`, divisor positive) -/

theorem ediv_le_of_le (x q d : ℤ) (hd : 0 < d) (h : x ≤ d * q + d - 1) :
    x / d ≤ q := by
  have h1 : x / d ≤ (d * q + d - 1) / d := Int.ediv_le_ediv hd h
  have h2 : (d - 1) / d = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [show d * q + d - 1 = (d - 1) + q * d by ring,
      Int.add_mul_ediv_right _ _ (by omega : d ≠ 0), h2, zero_add] at h1
  exact h1

theorem le_ediv_of_ge (x q d : ℤ) (hd : 0 < d) (h : d * q ≤ x) :
    q ≤ x / d :=
  (Int.le_ediv_iff_mul_le hd).mpr (by linarith [mul_comm d q])

end LeanNonlinearArith.Templates.Divisions

namespace LeanNonlinearArith.Templates.MonomialBounds

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## MB3 — even powers are nonnegative (infeasibility of negative upper) -/

theorem even_pow_nonneg (v : R) (p : ℕ) (hp : Even p) : 0 ≤ v ^ p :=
  hp.pow_nonneg v

/-! ## MB4 — upper root bounds -/

theorem le_of_odd_pow_le (v r : R) (p : ℕ) (hp : Odd p) (h : v ^ p ≤ r ^ p) :
    v ≤ r :=
  hp.pow_le_pow.mp h

theorem abs_le_of_even_pow_le (v r : R) (p : ℕ) (hp : Even p) (hp0 : p ≠ 0)
    (hr : 0 ≤ r) (h : v ^ p ≤ r ^ p) : -r ≤ v ∧ v ≤ r := by
  have habs : |v| ≤ r := by
    have h1 : |v| ^ p ≤ r ^ p := by
      rwa [hp.pow_abs]
    exact pow_le_pow_iff_left₀ (abs_nonneg v) hr hp0 |>.mp h1
  exact abs_le.mp habs

/-! ## MB5 — lower root bounds (even case genuinely disjunctive) -/

theorem ge_of_odd_pow_ge (v r : R) (p : ℕ) (hp : Odd p) (h : r ^ p ≤ v ^ p) :
    r ≤ v :=
  hp.pow_le_pow.mp h

theorem ge_or_le_of_even_pow_ge (v r : R) (p : ℕ) (hp : Even p) (hp0 : p ≠ 0)
    (hr : 0 ≤ r) (h : r ^ p ≤ v ^ p) : r ≤ v ∨ v ≤ -r := by
  have habs : r ≤ |v| := by
    have h1 : r ^ p ≤ |v| ^ p := by rwa [hp.pow_abs]
    exact pow_le_pow_iff_left₀ hr (abs_nonneg v) hp0 |>.mp h1
  rcases le_abs.mp habs with h' | h'
  · exact Or.inl h'
  · exact Or.inr (by linarith)

end LeanNonlinearArith.Templates.MonomialBounds
