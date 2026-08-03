import LeanNonlinearArith.Nlsat.Check

/-!
# nla-19a — checker pins (linearRoot slice)

End-to-end pins for the linearRoot discharge: coefficient extraction,
the emission reconstruction (F4), and the discharge itself on concrete
polynomials.
-/

namespace LeanNonlinearArith.Nlsat

open Check

/-- p = 2·y + x with y = var 1, x = var 0. Canonical: x-monomial
compares below y-monomial... storage order is `Monomial.cmp`
descending; [(y,1)] vs [(x,1)]: biggest var dominates, so y first. -/
def pLin : MPoly := [(2, [(1, 1)]), (1, [(0, 1)])]

/-- q = -3·y + 2 (const-lc negative → mkNeg variant). -/
def pLinNeg : MPoly := [(-3, [(1, 1)]), (2, [])]

-- coefficient extraction
example : coeffsOf pLin 1 = [[(1, [(0, 1)])], [(2, [])]] := by native_decide
example : coeffsOf pLinNeg 1 = [[(2, [])], [(-3, [])]] := by native_decide

-- degree guards
example : pLin.degreeIn 1 = 1 := by native_decide
example : pLinNeg.degreeIn 1 = 1 := by native_decide

-- canonicity (checker boundary, by decide)
theorem pLin_canon : ∀ t ∈ pLin, Monomial.Canon t.2 := by
  intro t ht
  simp only [pLin, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl <;> unfold Monomial.Canon <;> decide
theorem pLinNeg_canon : ∀ t ∈ pLinNeg, Monomial.Canon t.2 := by
  intro t ht
  simp only [pLinNeg, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl <;> unfold Monomial.Canon <;> decide

-- emission reconstruction (F4): kinds × polarity per the toIneqSign remap
example : linearRootEmitted .lt pLin false = (⟨.lt, [(pLin, false)]⟩, true) := rfl
example : linearRootEmitted .le pLin false = (⟨.gt, [(pLin, false)]⟩, false) := rfl
example : linearRootEmitted .ge pLinNeg true = (⟨.lt, [(pLinNeg.neg, false)]⟩, false) := rfl

/-- The discharge, positive-lc variant: `2y + x < 0` (the emitted
literal FAILING, i.e. the atom holding) ⟺ `ρ 1 < -(ρ 0)/2`. -/
example (ρ : Nat → ℝ) :
    ¬ SHolds ρ (linearRootEmitted .lt pLin false).1
      (linearRootEmitted .lt pLin false).2 ↔ ρ 1 < -ρ 0 / 2 := by
  have hA : evalP ρ ((coeffsOf pLin 1)[1]!) = 2 := by
    have : (coeffsOf pLin 1)[1]! = [(2, [])] := by native_decide
    rw [this]
    simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pLin 1)[0]!) = ρ 0 := by
    have : (coeffsOf pLin 1)[0]! = [(1, [(0, 1)])] := by native_decide
    rw [this]
    simp [evalP, evalM]
  rw [linearRoot_discharge ρ .lt 1 pLin false (by native_decide) pLin_canon
    (by rw [hA]; norm_num), hA, hC]
  exact Iff.rfl

/-- The discharge, negative-lc (mkNeg) variant: the folded atom
`-(-3y + 2) = 3y - 2 < 0` failing ⟺ `ρ 1 < 2/3`. -/
example (ρ : Nat → ℝ) :
    ¬ SHolds ρ (linearRootEmitted .lt pLinNeg true).1
      (linearRootEmitted .lt pLinNeg true).2 ↔ ρ 1 < -(2 : ℝ) / -3 := by
  have hA : evalP ρ ((coeffsOf pLinNeg 1)[1]!) = -3 := by
    have : (coeffsOf pLinNeg 1)[1]! = [(-3, [])] := by native_decide
    rw [this]
    simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pLinNeg 1)[0]!) = 2 := by
    have : (coeffsOf pLinNeg 1)[0]! = [(2, [])] := by native_decide
    rw [this]
    simp [evalP, evalM]
  rw [linearRoot_discharge ρ .lt 1 pLinNeg true (by native_decide) pLinNeg_canon
    (by rw [hA]; norm_num), hA, hC]
  exact Iff.rfl

/-- The GE remap: emitted (LT-atom, positive polarity) failing ⟺
`ρ 1 ≥ -(ρ 0)/2`. -/
example (ρ : Nat → ℝ) :
    ¬ SHolds ρ (linearRootEmitted .ge pLin false).1
      (linearRootEmitted .ge pLin false).2 ↔ -ρ 0 / 2 ≤ ρ 1 := by
  have hA : evalP ρ ((coeffsOf pLin 1)[1]!) = 2 := by
    have : (coeffsOf pLin 1)[1]! = [(2, [])] := by native_decide
    rw [this]
    simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pLin 1)[0]!) = ρ 0 := by
    have : (coeffsOf pLin 1)[0]! = [(1, [(0, 1)])] := by native_decide
    rw [this]
    simp [evalP, evalM]
  rw [linearRoot_discharge ρ .ge 1 pLin false (by native_decide) pLin_canon
    (by rw [hA]; norm_num), hA, hC]
  exact Iff.rfl

end LeanNonlinearArith.Nlsat
