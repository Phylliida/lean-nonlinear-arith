import Mathlib

/-!
# Templates: monotonicity lemmas (RULES.md rows M1–M2)

Schemas from `nla_monotone_lemmas.cpp`: magnitude bounds on factors give
magnitude bounds on the product. Binary steps compose to the n-ary clause the
generator emits.
-/

namespace LeanNonlinearArith.Templates.Monotone

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## M1 — upper: `|x| ≤ a ∧ |y| ≤ b → |xy| ≤ ab` -/

theorem abs_mul_le (x y a b : R) (hx : |x| ≤ a) (hy : |y| ≤ b) :
    |x * y| ≤ a * b := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) ((abs_nonneg x).trans hx)

/-- n-ary form over pairs `(xᵢ, boundᵢ)`. -/
theorem abs_prod_le (l : List (R × R)) (h : ∀ p ∈ l, |p.1| ≤ p.2) :
    |(l.map (·.1)).prod| ≤ (l.map (·.2)).prod := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    exact abs_mul_le _ _ _ _ (h p (by simp))
      (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

/-! ## M2 — lower: `|x| ≥ a ∧ |y| ≥ b → |xy| ≥ ab` (bounds nonneg) -/

theorem abs_mul_ge (x y a b : R) (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : a ≤ |x|) (hy : b ≤ |y|) : a * b ≤ |x * y| := by
  rw [abs_mul]
  exact mul_le_mul hx hy hb (abs_nonneg x)

theorem abs_prod_ge (l : List (R × R)) (hnn : ∀ p ∈ l, 0 ≤ p.2)
    (h : ∀ p ∈ l, p.2 ≤ |p.1|) :
    (l.map (·.2)).prod ≤ |(l.map (·.1)).prod| := by
  induction l with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    have hb : (0 : R) ≤ (ps.map (·.2)).prod :=
      List.prod_nonneg (by
        intro x hx
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
        exact hnn q (List.mem_cons_of_mem _ hq))
    exact abs_mul_ge _ _ _ _ (hnn p (by simp)) hb (h p (by simp))
      (ih (fun q hq => hnn q (List.mem_cons_of_mem _ hq))
          (fun q hq => h q (List.mem_cons_of_mem _ hq)))

end LeanNonlinearArith.Templates.Monotone
