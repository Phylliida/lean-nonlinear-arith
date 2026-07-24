import Mathlib

/-!
# Templates: basics (RULES.md rows B1–B10)

Proven lemma families for the schemas emitted by `nla_basics_lemmas.cpp`.
Rows discharged at instantiation time by `subst`+`ring` (B9, and the module
rows T1/PL1) need no schema lemma; everything else is here.
-/

namespace LeanNonlinearArith.Templates.Basics

variable {R : Type*} [CommRing R]

/-! ## B3 / B4 / B10 — a zero factor kills the product -/

theorem zero_factor (x y : R) (h : x = 0) : x * y = 0 := by
  rw [h, zero_mul]

theorem zero_factor_list (l : List R) (h : (0 : R) ∈ l) : l.prod = 0 :=
  List.prod_eq_zero h

/-! ## B5 — product zero forces a zero factor (no zero divisors) -/

theorem prod_zero_factor {S : Type*} [CommMonoidWithZero S] [NoZeroDivisors S]
    [Nontrivial S] (l : List S) (h : l.prod = 0) : (0 : S) ∈ l :=
  List.prod_eq_zero_iff.mp h

/-! ## B1 — sign lemma: products agree up to an aggregate sign

Z3's `generate_sign_lemma` asserts `m = s·n` when factor lists agree pairwise
up to signs. Stated over a list of triples `(aᵢ, σᵢ, bᵢ)` with `aᵢ = σᵢ·bᵢ`;
±1-ness of the σᵢ is not needed for validity, so it is not assumed. -/

theorem prod_eq_signs_mul_prod (l : List (R × R × R))
    (h : ∀ t ∈ l, t.1 = t.2.1 * t.2.2) :
    (l.map (·.1)).prod = (l.map (·.2.1)).prod * (l.map (·.2.2)).prod := by
  induction l with
  | nil => simp
  | cons t ts ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [h t (by simp), ih (fun t' ht' => h t' (List.mem_cons_of_mem _ ht'))]
    ring

/-! ## B2 — strict factor signs determine the strict sign of the product -/

theorem prod_pos_of_all_pos {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (l : List S) (h : ∀ x ∈ l, 0 < x) : 0 < l.prod :=
  List.prod_pos h

/-- Parity form: with all factors nonzero, the product is positive iff the
number of negative factors is even. -/
theorem prod_pos_iff_even_negs {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]
    (l : List S) (h : ∀ x ∈ l, x ≠ 0) :
    0 < l.prod ↔ Even (l.countP (fun x => decide (x < 0))) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≠ 0 := h a (by simp)
    have ht : ∀ x ∈ t, x ≠ 0 := fun x hx => h x (List.mem_cons_of_mem _ hx)
    have htp : t.prod ≠ 0 := fun h0 => (ht 0 (prod_zero_factor t h0)) rfl
    have iht := ih ht
    simp only [List.prod_cons, List.countP_cons]
    rcases lt_trichotomy a 0 with hneg | hzero | hpos
    · have hd : decide (a < 0) = true := by simp [hneg]
      rw [hd, if_pos rfl]
      rw [Nat.even_add_one, ← iht]
      constructor
      · intro hp hq
        rcases mul_pos_iff.mp hp with ⟨ha', _⟩ | ⟨_, hb'⟩
        · exact absurd ha' (not_lt.mpr hneg.le)
        · exact absurd hq (not_lt.mpr hb'.le)
      · intro hnp
        have htneg : t.prod < 0 := lt_of_le_of_ne (not_lt.mp hnp) htp
        exact mul_pos_of_neg_of_neg hneg htneg
    · exact absurd hzero ha
    · have hd : decide (a < 0) = false := by simp [not_lt.mpr hpos.le]
      rw [hd, if_neg (by simp), Nat.add_zero, ← iht]
      constructor
      · intro hp
        rcases mul_pos_iff.mp hp with ⟨_, hb'⟩ | ⟨ha', _⟩
        · exact hb'
        · exact absurd hpos (not_lt.mpr ha'.le)
      · exact fun hp => mul_pos hpos hp

/-! ## B7 — neutral factor: |x·a| = |x|, x ≠ 0 forces a = ±1 (integers) -/

theorem neutral_factor (x a : ℤ) (hx : x ≠ 0) (h : |x * a| = |x|) :
    a = 1 ∨ a = -1 := by
  rw [abs_mul] at h
  have hxa : |x| ≠ 0 := fun h0 => hx (abs_eq_zero.mp h0)
  have h1 : |a| = 1 := mul_left_cancel₀ hxa (h.trans (mul_one _).symm)
  exact (abs_eq (by norm_num)).mp h1

/-! ## B8 — proportion: nonzero integer cofactors only grow magnitude -/

theorem abs_le_abs_mul_of_ne_zero (a b : ℤ) (ha : a ≠ 0) : |b| ≤ |a * b| := by
  rw [abs_mul]
  calc |b| = 1 * |b| := (one_mul _).symm
    _ ≤ |a| * |b| := mul_le_mul_of_nonneg_right (Int.one_le_abs ha) (abs_nonneg b)

end LeanNonlinearArith.Templates.Basics
