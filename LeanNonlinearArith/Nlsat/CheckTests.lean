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
theorem pLin_canon : MPoly.Canon pLin :=
  MPoly.canon_two 2 [(1, 1)] 1 [(0, 1)] (by decide) (by unfold Monomial.Canon; decide)
    (by decide) (by unfold Monomial.Canon; decide) (by native_decide)
theorem pLinNeg_canon : MPoly.Canon pLinNeg :=
  MPoly.canon_two (-3) [(1, 1)] 2 [] (by decide) (by unfold Monomial.Canon; decide)
    (by decide) (by unfold Monomial.Canon; decide) (by native_decide)

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

theorem pQuad_canon : MPoly.Canon pQuad :=
  MPoly.canon_two 1 [(1, 2)] (-2) [] (by decide) (by unfold Monomial.Canon; decide)
    (by decide) (by unfold Monomial.Canon; decide) (by native_decide)

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


/-! ## cellBound slice pins -/

/-- cellBound over a linear encoding: from the emitted literal failing
(`2y + x < 0` holding) to the ordering `ρ 1 < rootVal` — which computes
to `-(ρ 0)/2`. -/
example (ρ : Nat → ℝ) (hfails : IneqAtom.Holds ρ ⟨.lt, [(pLin, false)]⟩) :
    rootCmp .lt (ρ 1) (rootVal ρ 1 1 pLin) := by
  have hA : evalP ρ ((coeffsOf pLin 1)[1]!) = 2 := by
    have : (coeffsOf pLin 1)[1]! = [(2, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  exact cellBound_linear ρ .lt 1 1 pLin false (by native_decide) pLin_canon
    (by rw [hA]; norm_num)
    (by simpa [linearRootEmitted, RootKind.toIneqSign, SHolds] using hfails)

/-- The same ordering through `rootVal`: the value is `-C/A`. -/
example (ρ : Nat → ℝ) :
    rootVal ρ 1 1 pLin = -ρ 0 / 2 := by
  have hA : evalP ρ ((coeffsOf pLin 1)[1]!) = 2 := by
    have : (coeffsOf pLin 1)[1]! = [(2, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pLin 1)[0]!) = ρ 0 := by
    have : (coeffsOf pLin 1)[0]! = [(1, [(0, 1)])] := by native_decide
    rw [this]; simp [evalP, evalM]
  rw [rootVal_eq_linear ρ 1 1 pLin (by native_decide), hA, hC]

/-- cellBound over a Thom encoding: the region formula `p > 0 ∧
pDiff > 0` gives `ρ 1 > root₂(y² − 2)`. -/
example (ρ : Nat → ℝ)
    (hform : thomFormula .gt 2
      (leadSgn (evalP ρ ((coeffsOf pQuad 1)[2]!)) * evalP ρ pQuad)
      (leadSgn (evalP ρ ((coeffsOf pQuad 1)[2]!)) *
        (2 * evalP ρ ((coeffsOf pQuad 1)[2]!) * ρ 1 + evalP ρ ((coeffsOf pQuad 1)[1]!)))) :
    rootCmp .gt (ρ 1) (rootVal ρ 1 2 pQuad) := by
  have hA : evalP ρ ((coeffsOf pQuad 1)[2]!) = 1 := by
    have : (coeffsOf pQuad 1)[2]! = [(1, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hB : evalP ρ ((coeffsOf pQuad 1)[1]!) = 0 := by
    have : (coeffsOf pQuad 1)[1]! = [] := by native_decide
    rw [this]; simp [evalP]
  have hC : evalP ρ ((coeffsOf pQuad 1)[0]!) = -2 := by
    have : (coeffsOf pQuad 1)[0]! = [(-2, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  exact cellBound_thom ρ .gt 1 2 pQuad 1 1 (by native_decide) (Or.inr rfl)
    pQuad_canon (by decide)
    (by rw [hA]; exact Or.inr (Or.inr ⟨rfl, by norm_num⟩)) (Or.inr rfl)
    (by rw [hB, hA, hC]; exact Or.inr (Or.inr ⟨rfl, by norm_num⟩))
    hform


/-! ## leafNumeric slice pins -/

def pX : MPoly := [(1, [(0, 1)])]
def pXsq : MPoly := [(1, [(0, 2)])]

/-- The stage-1 leaf of the x²+y²<0 refutation (the actual final
conflict from the search): the learned clause `x₀ < 0 ∨ x₀² = 0 ∨
x₀ > 0` is valid over ℝ — the v0 glue-level discharge (trichotomy +
atom semantics). Higher-degree leaves discharge via `CertGen`
certificates at check time (Slice F). -/
example (ρ : Nat → ℝ) :
    IneqAtom.Holds ρ ⟨.lt, [(pX, false)]⟩ ∨
    IneqAtom.Holds ρ ⟨.eq, [(pXsq, false)]⟩ ∨
    IneqAtom.Holds ρ ⟨.gt, [(pX, false)]⟩ := by
  have e1 : evalP ρ pX = ρ 0 := by simp [pX, evalP, evalM]
  have e2 : evalP ρ pXsq = (ρ 0)^2 := by simp [pXsq, evalP, evalM]
  rcases lt_trichotomy (ρ 0) 0 with h | h | h
  · exact Or.inl ((holds_single_lt ρ pX).mpr (by rw [e1]; exact h))
  · exact Or.inr (Or.inl ((holds_single_eq ρ pXsq).mpr (by rw [e2, h]; simp)))
  · exact Or.inr (Or.inr ((holds_single_gt ρ pX).mpr (by rw [e1]; exact h)))

/-- The full learned-clause-as-iff form: `(x₀² = 0) ↔ (x₀ = 0)` makes
the disjunction exactly trichotomy. -/
example (ρ : Nat → ℝ) :
    IneqAtom.Holds ρ ⟨.eq, [(pXsq, false)]⟩ ↔ IneqAtom.Holds ρ ⟨.eq, [(pX, false)]⟩ := by
  have e1 : evalP ρ pX = ρ 0 := by simp [pX, evalP, evalM]
  have e2 : evalP ρ pXsq = (ρ 0)^2 := by simp [pXsq, evalP, evalM]
  rw [holds_single_eq, holds_single_eq, e1, e2, sq_eq_zero_iff]


/-! ## R2/R3 pins (design review 2) -/

/-- R3: the coeffsOf↔coeffsIn bridge, applied. -/
example : coeffsOf pQuad2 1 = (pQuad2.coeffsIn 1).toList :=
  coeffsOf_eq_coeffsIn_toList pQuad2 1
example : coeffsOf pLin 1 = (pLin.coeffsIn 1).toList :=
  coeffsOf_eq_coeffsIn_toList pLin 1

/-- p = y² + 1 (var 1): disc = −4 < 0 ⇒ no roots ⇒ atom false. -/
def pNoRoots : MPoly := [(1, [(1, 2)]), (1, [])]

example (ρ : Nat → ℝ) : ¬ RootAtom.Holds ρ ⟨.gt, 1, 1, pNoRoots⟩ := by
  have hB : evalP ρ ((coeffsOf pNoRoots 1)[1]!) = 0 := by
    have : (coeffsOf pNoRoots 1)[1]! = [] := by native_decide
    rw [this]; simp [evalP]
  have hA : evalP ρ ((coeffsOf pNoRoots 1)[2]!) = 1 := by
    have : (coeffsOf pNoRoots 1)[2]! = [(1, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pNoRoots 1)[0]!) = 1 := by
    have : (coeffsOf pNoRoots 1)[0]! = [(1, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hdisc : evalP ρ ((coeffsOf pNoRoots 1)[1]!)^2 -
      4 * evalP ρ ((coeffsOf pNoRoots 1)[2]!) * evalP ρ ((coeffsOf pNoRoots 1)[0]!)
      < 0 := by
    rw [hB, hA, hC]; norm_num
  exact rootAtom_false_of_index_lt ρ .gt 1 1 pNoRoots
    (by rw [rootCount_zero_of_neg_disc ρ 1 pNoRoots (by native_decide) hdisc]
        decide)

/-- i = 3 exceeds the root count (2) of y² − 2 ⇒ atom false (z3's
`i > roots.size()` rule). -/
example (ρ : Nat → ℝ) : ¬ RootAtom.Holds ρ ⟨.lt, 1, 3, pQuad⟩ := by
  have hB : evalP ρ ((coeffsOf pQuad 1)[1]!) = 0 := by
    have : (coeffsOf pQuad 1)[1]! = [] := by native_decide
    rw [this]; simp [evalP]
  have hA : evalP ρ ((coeffsOf pQuad 1)[2]!) = 1 := by
    have : (coeffsOf pQuad 1)[2]! = [(1, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pQuad 1)[0]!) = -2 := by
    have : (coeffsOf pQuad 1)[0]! = [(-2, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hcount : rootCount ρ 1 pQuad = 2 := by
    unfold rootCount
    rw [if_neg (by native_decide : ¬(pQuad.degreeIn 1 = 1)),
        if_pos (by rw [hA]; norm_num), hB, hA, hC]
    norm_num
  exact rootAtom_false_of_index_lt ρ .lt 1 3 pQuad (by rw [hcount]; decide)

/-- deg-1 root atom semantics: `root₁(2y + x)` exists (lc ≠ 0) and
`y > root₁` ⟺ `ρ 1 > -(ρ 0)/2`. -/
example (ρ : Nat → ℝ) :
    RootAtom.Holds ρ ⟨.gt, 1, 1, pLin⟩ ↔ -ρ 0 / 2 < ρ 1 := by
  have hA : evalP ρ ((coeffsOf pLin 1)[1]!) = 2 := by
    have : (coeffsOf pLin 1)[1]! = [(2, [])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hC : evalP ρ ((coeffsOf pLin 1)[0]!) = ρ 0 := by
    have : (coeffsOf pLin 1)[0]! = [(1, [(0, 1)])] := by native_decide
    rw [this]; simp [evalP, evalM]
  have hcount : rootCount ρ 1 pLin = 1 := by
    unfold rootCount
    rw [if_pos (by native_decide : pLin.degreeIn 1 = 1), hA]
    norm_num
  rw [RootAtom.Holds, hcount, rootVal_eq_linear ρ 1 1 pLin (by native_decide), hC, hA]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨Nat.le_refl 1, h⟩

end LeanNonlinearArith.Nlsat
