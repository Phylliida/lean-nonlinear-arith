import Mathlib

/-!
# Templates: interval arithmetic (RULES.md rows MB1–MB2, H1)

Soundness of interval product/sum bounds: the schemas behind
`monomial_bounds.cpp` value propagation (MB1–2) and, step by step, the Horner
interval evaluation of `horner.cpp` (H1) — every Horner step is one
`mem_intervalAdd` and one `mem_intervalMul` instance.

Intervals are plain pairs `(lo, hi)`; membership is `lo ≤ x ∧ x ≤ hi`.
-/

namespace LeanNonlinearArith.Templates.Intervals

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Interval membership. -/
def Mem (x : R) (i : R × R) : Prop := i.1 ≤ x ∧ x ≤ i.2

/-- Interval product: corner min/max. -/
def intervalMul (i j : R × R) : R × R :=
  (min (min (i.1 * j.1) (i.1 * j.2)) (min (i.2 * j.1) (i.2 * j.2)),
   max (max (i.1 * j.1) (i.1 * j.2)) (max (i.2 * j.1) (i.2 * j.2)))

/-- Interval sum. -/
def intervalAdd (i j : R × R) : R × R := (i.1 + j.1, i.2 + j.2)

/-! ## Binary soundness -/

theorem mem_intervalAdd {x y : R} {i j : R × R}
    (hx : Mem x i) (hy : Mem y j) : Mem (x + y) (intervalAdd i j) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem mul_le_max_corners {x y lo₁ hi₁ lo₂ hi₂ : R}
    (hx₁ : lo₁ ≤ x) (hx₂ : x ≤ hi₁) (hy₁ : lo₂ ≤ y) (hy₂ : y ≤ hi₂) :
    x * y ≤ max (max (lo₁ * lo₂) (lo₁ * hi₂)) (max (hi₁ * lo₂) (hi₁ * hi₂)) := by
  have step1 : x * y ≤ max (lo₁ * y) (hi₁ * y) := by
    rcases le_or_gt 0 y with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hx₂ h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_right hx₁ h.le)
  have step2 : lo₁ * y ≤ max (lo₁ * lo₂) (lo₁ * hi₂) := by
    rcases le_or_gt 0 lo₁ with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hy₂ h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hy₁ h.le)
  have step3 : hi₁ * y ≤ max (hi₁ * lo₂) (hi₁ * hi₂) := by
    rcases le_or_gt 0 hi₁ with h | h
    · exact le_max_of_le_right (mul_le_mul_of_nonneg_left hy₂ h)
    · exact le_max_of_le_left (mul_le_mul_of_nonpos_left hy₁ h.le)
  exact step1.trans (max_le_max step2 step3)

theorem min_corners_le_mul {x y lo₁ hi₁ lo₂ hi₂ : R}
    (hx₁ : lo₁ ≤ x) (hx₂ : x ≤ hi₁) (hy₁ : lo₂ ≤ y) (hy₂ : y ≤ hi₂) :
    min (min (lo₁ * lo₂) (lo₁ * hi₂)) (min (hi₁ * lo₂) (hi₁ * hi₂)) ≤ x * y := by
  have step1 : min (lo₁ * y) (hi₁ * y) ≤ x * y := by
    rcases le_or_gt 0 y with h | h
    · exact min_le_of_left_le (mul_le_mul_of_nonneg_right hx₁ h)
    · exact min_le_of_right_le (mul_le_mul_of_nonpos_right hx₂ h.le)
  have step2 : min (lo₁ * lo₂) (lo₁ * hi₂) ≤ lo₁ * y := by
    rcases le_or_gt 0 lo₁ with h | h
    · exact min_le_of_left_le (mul_le_mul_of_nonneg_left hy₁ h)
    · exact min_le_of_right_le (mul_le_mul_of_nonpos_left hy₂ h.le)
  have step3 : min (hi₁ * lo₂) (hi₁ * hi₂) ≤ hi₁ * y := by
    rcases le_or_gt 0 hi₁ with h | h
    · exact min_le_of_left_le (mul_le_mul_of_nonneg_left hy₁ h)
    · exact min_le_of_right_le (mul_le_mul_of_nonpos_left hy₂ h.le)
  exact (min_le_min step2 step3).trans step1

theorem mem_intervalMul {x y : R} {i j : R × R}
    (hx : Mem x i) (hy : Mem y j) : Mem (x * y) (intervalMul i j) :=
  ⟨min_corners_le_mul hx.1 hx.2 hy.1 hy.2,
   mul_le_max_corners hx.1 hx.2 hy.1 hy.2⟩

/-! ## n-ary product (MB1–2's monomial form) -/

/-- Interval product of a list of intervals. -/
def intervalProd : List (R × R) → R × R
  | [] => (1, 1)
  | i :: is => intervalMul i (intervalProd is)

/-- Soundness: a product of factors lies in the interval product of their
intervals. Stated over pairs `(factor, interval)`. -/
theorem mem_intervalProd (l : List (R × (R × R)))
    (h : ∀ p ∈ l, Mem p.1 p.2) :
    Mem (l.map (·.1)).prod (intervalProd (l.map (·.2))) := by
  induction l with
  | nil => exact ⟨le_refl 1, le_refl 1⟩
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    exact mem_intervalMul (h p (by simp))
      (ih (fun q hq => h q (List.mem_cons_of_mem _ hq)))

end LeanNonlinearArith.Templates.Intervals
