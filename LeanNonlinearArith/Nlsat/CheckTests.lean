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

/-! ## thomQuadratic slice pins -/

open LeanNonlinearArith.Templates.Quadratic

/-- p = y² − 2 (y = var 1). -/
def pQuad : MPoly := [(1, [(1, 2)]), (-2, [])]

/-- p = y² + x·y + x² (x = var 0) — nonzero B, lower-var coeffs. -/
def pQuad2 : MPoly := [(1, [(1, 2)]), (1, [(0, 1), (1, 1)]), (1, [(0, 2)])]

-- coefficient extraction
example : coeffsOf pQuad 1 = [[(-2, [])], [], [(1, [])]] := by native_decide
example : (coeffsOf pQuad2 1)[1]! = [(1, [(0, 1)])] := by native_decide

/-- The emission-side constructions (`mkQuadraticRoot` uses `coeffsIn`;
the checker's `coeffsOf` must agree BY VALUE — the F4 reconstruction
contract). -/
def emissionDisc (p : MPoly) (y : Var) : MPoly :=
  let cs := p.coeffsIn y
  ((cs[1]!).mul (cs[1]!)).sub ((MPoly.ofInt 4).mul ((cs[2]!).mul (cs[0]!)))
def emissionPDiff (p : MPoly) (y : Var) : MPoly :=
  let cs := p.coeffsIn y
  MPoly.managerNormalize none
    (MPoly.add (MPoly.mul (MPoly.smulTerm 2 [] (cs[2]!)) (MPoly.ofVar y)) (cs[1]!))

example : discPolyOf pQuad 1 = emissionDisc pQuad 1 := by native_decide
example : pDiffPolyOf pQuad 1 = emissionPDiff pQuad 1 := by native_decide
example : discPolyOf pQuad2 1 = emissionDisc pQuad2 1 := by native_decide
example : pDiffPolyOf pQuad2 1 = emissionPDiff pQuad2 1 := by native_decide

-- discPolyOf computes: disc(y² − 2) = 0² − 4·1·(−2) = 8
example : discPolyOf pQuad 1 = [(8, [])] := by native_decide
-- pDiffPolyOf computes: 2y normalized by content 2 → y
example : pDiffPolyOf pQuad 1 = [(1, [(1, 1)])] := by native_decide

theorem pQuad_canon : ∀ t ∈ pQuad, Monomial.Canon t.2 := by
  intro t ht
  simp only [pQuad, List.mem_cons, List.mem_nil_iff, or_false] at ht
  rcases ht with rfl | rfl <;> unfold Monomial.Canon <;> decide

/-- The Thom discharge, applied: `ρ 1 > root₂(y² − 2)` ⟺ the region
formula `p > 0 ∧ pDiff > 0` (positive lead, disc = 8 > 0). -/
example (ρ : Nat → ℝ) :
    rootCmp .gt (ρ 1) (quadRootVal 2
        (evalP ρ ((coeffsOf pQuad 1)[2]!)) (evalP ρ ((coeffsOf pQuad 1)[1]!))
        (evalP ρ ((coeffsOf pQuad 1)[0]!))) ↔
      (0 < evalP ρ pQuad ∧ 0 < 2 * ρ 1) := by
  have hA : evalP ρ ((coeffsOf pQuad 1)[2]!) = 1 := by
    have : (coeffsOf pQuad 1)[2]! = [(1, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hB : evalP ρ ((coeffsOf pQuad 1)[1]!) = 0 := by
    have : (coeffsOf pQuad 1)[1]! = [] := by native_decide
    rw [this]; simp [evalP]
  have hC : evalP ρ ((coeffsOf pQuad 1)[0]!) = -2 := by
    have : (coeffsOf pQuad 1)[0]! = [(-2, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hmain := thom_discharge ρ .gt 1 2 pQuad 1 1 (by native_decide) (Or.inr rfl)
    pQuad_canon (by decide)
    (by rw [hA]; exact Or.inr (Or.inr ⟨rfl, by norm_num⟩)) (Or.inr rfl)
    (by rw [hB, hA, hC]; exact Or.inr (Or.inr ⟨rfl, by norm_num⟩))
  have hsgn : leadSgn (1 : ℝ) = 1 := by simp [leadSgn]
  rw [hA, hB, hC] at hmain
  rw [hsgn, one_mul, one_mul] at hmain
  rw [hA, hB, hC]
  rw [hmain]
  show (0 < evalP ρ pQuad ∧ 0 < (2 * 1 * ρ 1 + 0)) ↔ _
  rw [show (2 * 1 * ρ 1 + 0 : ℝ) = 2 * ρ 1 by ring]

/-- The root value computes: `root₂(y² − 2) = √2`. -/
example : quadRootVal 2 (1 : ℝ) 0 (-2) = Real.sqrt 2 := by
  have hsgn : leadSgn (1 : ℝ) = 1 := by simp [leadSgn]
  simp only [quadRootVal, hsgn, one_mul]
  unfold quadRoot
  have hd : (0 : ℝ)^2 - 4 * 1 * -2 = 8 := by norm_num
  have hif : (if 2 = 1 then (-1 : ℝ) else 1) = 1 := by norm_num
  rw [hd, hif]
  have hsqrt8 : Real.sqrt 8 = 2 * Real.sqrt 2 := by
    rw [show (8 : ℝ) = 2^2 * 2 by norm_num,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2^2),
        Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  rw [hsqrt8]
  field_simp
  ring

end LeanNonlinearArith.Nlsat
