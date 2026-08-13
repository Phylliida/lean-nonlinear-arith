import LeanNonlinearArith.Nlsat.Check.Semantics
import LeanNonlinearArith.Nlsat.MPolyOps
import LeanNonlinearArith.Nlsat.MPolyZp

/-!
# nla-19a — the checker, discharge layer (TRUSTED)

The per-step discharge theorems of the trace contract, split out of
`Check.lean` at F5 (R8 of design review 3). Semantics live in
`Check/Semantics.lean`; this file composes them into the per-step
obligations:

1. **The linearRoot discharge** (z3 `mk_linear_root` :861-878): the
   root of `a·y + c` is `-c/a`, and the emitted sign literal on the
   `mkNeg`-folded poly is exactly the root comparison — incl. the
   LE/GE kind remap + literal-negation fold.
2. **The Thom discharge** (z3 `mk_quadratic_root` :787-820):
   `thom_iff` — the whole content of the quadratic encoding's
   correctness, first-order via `4a·p = (2ay+b)² − disc` — plus the
   `discPolyOf`/`pDiffPolyOf` reconstruction bridges (incl. the
   `managerNormalize` sign-transfer).
3. **The cellBound wrappers**: thin repackagings at the `rootVal`
   level (the mathematical content is in the encoding discharges).
4. **The rootGeneric discharge** + the `rootCount` corner theorems
   (definite-disc `rootCount = 0`, index-beyond-count atom-false).
-/

namespace LeanNonlinearArith.Nlsat

namespace Check

/-! ## The linearRoot discharge (z3 `mk_linear_root` :861-878) -/

/-- The atom + polarity a `linearRoot` step emits (the F4
reconstruction): `add_simple_assumption k' q lsign` with
`(k', lsign) = k.toIneqSign`, `q = mkNeg ? -p : p`. -/
def linearRootEmitted (k : RootKind) (p : MPoly) (mkNeg : Bool) : IneqAtom × Bool :=
  let (k', lsign) := k.toIneqSign
  (⟨k', [(if mkNeg then p.neg else p, false)]⟩, !lsign)

/-- Root of `a·Y + c`: the point is the root iff the value vanishes. -/
theorem lin_root_eq {A C : ℝ} (hA : A ≠ 0) (Y : ℝ) :
    A * Y + C = 0 ↔ Y = -C / A := by
  rw [eq_div_iff hA]
  constructor <;> intro h <;> linarith

/-- Positive lead: the value is negative left of the root. -/
theorem lin_root_lt {A C : ℝ} (hA : 0 < A) (Y : ℝ) :
    A * Y + C < 0 ↔ Y < -C / A := by
  constructor
  · intro h
    rw [lt_div_iff₀ hA]
    linarith
  · intro h
    rw [lt_div_iff₀ hA] at h
    linarith

/-- Positive lead: the value is positive right of the root. -/
theorem lin_root_gt {A C : ℝ} (hA : 0 < A) (Y : ℝ) :
    0 < A * Y + C ↔ -C / A < Y := by
  constructor
  · intro h
    rw [div_lt_iff₀ hA]
    linarith
  · intro h
    rw [div_lt_iff₀ hA] at h
    linarith

theorem lin_root_le {A C : ℝ} (hA : 0 < A) (Y : ℝ) :
    A * Y + C ≤ 0 ↔ Y ≤ -C / A := by
  rw [← not_lt, lin_root_gt hA Y, not_lt]

theorem lin_root_ge {A C : ℝ} (hA : 0 < A) (Y : ℝ) :
    0 ≤ A * Y + C ↔ -C / A ≤ Y := by
  rw [← not_lt, lin_root_lt hA Y, not_lt]

/-- The discharge: the emitted literal FAILS at `ρ` exactly when `ρ y`
bears the root comparison to `-C/A` (the root of `p` in `y`). `hAq` is
the leading-coefficient positivity evidence (const-lc variant: by
`decide` on the const value + the `mkNeg` fold; `mk_plinear_root`
variant: from the `lcFact` sign literal failing at `ρ`). -/
theorem linearRoot_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var) (p : MPoly)
    (mkNeg : Bool)
    (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (hAq : (0 : ℝ) < (if mkNeg then (-1 : ℝ) else 1) * evalP ρ ((coeffsOf p y)[1]!)) :
    ¬ SHolds ρ (linearRootEmitted k p mkNeg).1 (linearRootEmitted k p mkNeg).2 ↔
      rootCmp k (ρ y)
        (-evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!)) := by
  have hform := evalP_linear_form ρ y p hdeg hcan
  set A := evalP ρ ((coeffsOf p y)[1]!)
  set C := evalP ρ ((coeffsOf p y)[0]!)
  set s : ℝ := if mkNeg then (-1 : ℝ) else 1
  have hsA : (0 : ℝ) < s * A := hAq
  have hsAne : s * A ≠ 0 := ne_of_gt hsA
  have hq : evalP ρ (if mkNeg then p.neg else p) = (s * A) * ρ y + (s * C) := by
    cases mkNeg <;> simp [s, evalP_neg, hform] <;> ring
  have hroot : -(s * C) / (s * A) = -C / A := by
    have hsne : s ≠ 0 := by
      intro h; rw [h, zero_mul] at hsA; exact (lt_irrefl 0) hsA
    have hAne : A ≠ 0 := by
      intro h; rw [h, mul_zero] at hsA; exact (lt_irrefl 0) hsA
    cases mkNeg <;> simp [s] <;> field_simp <;> ring
  cases k with
  | eq =>
    have he : linearRootEmitted .eq p mkNeg =
        (⟨.eq, [(if mkNeg then p.neg else p, false)]⟩, true) := rfl
    rw [he]
    show (¬ ¬ IneqAtom.Holds ρ ⟨.eq, [(if mkNeg then p.neg else p, false)]⟩) ↔ _
    rw [not_not, holds_single_eq, hq, lin_root_eq hsAne (ρ y), hroot]
    exact Iff.rfl
  | lt =>
    have he : linearRootEmitted .lt p mkNeg =
        (⟨.lt, [(if mkNeg then p.neg else p, false)]⟩, true) := rfl
    rw [he]
    show (¬ ¬ IneqAtom.Holds ρ ⟨.lt, [(if mkNeg then p.neg else p, false)]⟩) ↔ _
    rw [not_not, holds_single_lt, hq, lin_root_lt hsA (ρ y), hroot]
    exact Iff.rfl
  | gt =>
    have he : linearRootEmitted .gt p mkNeg =
        (⟨.gt, [(if mkNeg then p.neg else p, false)]⟩, true) := rfl
    rw [he]
    show (¬ ¬ IneqAtom.Holds ρ ⟨.gt, [(if mkNeg then p.neg else p, false)]⟩) ↔ _
    rw [not_not, holds_single_gt, hq, lin_root_gt hsA (ρ y), hroot]
    exact Iff.rfl
  | le =>
    have he : linearRootEmitted .le p mkNeg =
        (⟨.gt, [(if mkNeg then p.neg else p, false)]⟩, false) := rfl
    rw [he]
    show (¬ IneqAtom.Holds ρ ⟨.gt, [(if mkNeg then p.neg else p, false)]⟩) ↔ _
    rw [holds_single_gt, not_lt, hq, lin_root_le hsA (ρ y), hroot]
    exact Iff.rfl
  | ge =>
    have he : linearRootEmitted .ge p mkNeg =
        (⟨.lt, [(if mkNeg then p.neg else p, false)]⟩, false) := rfl
    rw [he]
    show (¬ IneqAtom.Holds ρ ⟨.lt, [(if mkNeg then p.neg else p, false)]⟩) ↔ _
    rw [holds_single_lt, not_lt, hq, lin_root_ge hsA (ρ y), hroot]
    exact Iff.rfl



open LeanNonlinearArith.Templates.Quadratic

theorem quadRoot_le {A B C : ℝ} (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C) :
    quadRoot 1 A B C ≤ quadRoot 2 A B C := by
  rcases eq_or_lt_of_le hd with hdz | hd'
  · rw [quadRoot_eq_of_disc_zero (ne_of_gt hA) hdz.symm 1,
        quadRoot_eq_of_disc_zero (ne_of_gt hA) hdz.symm 2]
  · exact le_of_lt (quadRoot_lt hA hd')

/-- The master Thom equivalence (positive lead): the root comparison is
the region formula. This is the whole content of `mk_quadratic_root`'s
correctness, first-order via the one identity. -/
theorem thom_iff {A B C : ℝ} (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C)
    {i : Nat} (hi : i = 1 ∨ i = 2) (k : RootKind) (y : ℝ) :
    rootCmp k y (quadRoot i A B C) ↔
      thomFormula k i (A * y^2 + B * y + C) (2 * A * y + B) := by
  have hAne : A ≠ 0 := ne_of_gt hA
  have hle : quadRoot 1 A B C ≤ quadRoot 2 A B C := quadRoot_le hA hd
  rcases hi with rfl | rfl
  · cases k with
    | eq =>
      show (y = quadRoot 1 A B C) ↔ (A * y^2 + B * y + C = 0 ∧ 2 * A * y + B ≤ 0)
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · rw [h]
          exact quadRoot_is_root hAne hd 1
        · have hr := twoA_mul_quadRoot_add (B := B) (C := C) hAne 1
          have hr2x : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by simpa using hr
          have := Real.sqrt_nonneg (B^2 - 4*A*C)
          rw [h, hr2x]
          linarith
      · intro ⟨hp, hpd⟩
        exact (eq_quadRoot1_iff hA hd hp).mpr hpd
    | lt =>
      show (y < quadRoot 1 A B C) ↔ (0 < A * y^2 + B * y + C ∧ 2 * A * y + B < 0)
      exact lt_quadRoot1_iff hA hd y
    | gt =>
      show (quadRoot 1 A B C < y) ↔
        (A * y^2 + B * y + C < 0 ∨ (0 ≤ A * y^2 + B * y + C ∧ 0 < 2 * A * y + B))
      constructor
      · intro hy
        rcases lt_trichotomy (A * y^2 + B * y + C) 0 with hp | hp | hp
        · exact Or.inl hp
        · -- p = 0: y ∈ {r₁, r₂}, and y > r₁ forces y = r₂ with pd > 0
          have hroots : y = quadRoot 1 A B C ∨ y = quadRoot 2 A B C := by
            rcases le_or_lt (2 * A * y + B) 0 with hpd | hpd
            · exact Or.inl ((eq_quadRoot1_iff hA hd hp).mpr hpd)
            · exact Or.inr ((eq_quadRoot2_iff hA hd hp).mpr (le_of_lt hpd))
          rcases hroots with rfl | rfl
          · exact absurd hy (lt_irrefl _)
          · have hd' : 0 < B^2 - 4*A*C := by
              by_contra hc
              push_neg at hc
              have hdz : B^2 - 4*A*C = 0 := le_antisymm hc hd
              rw [quadRoot_eq_of_disc_zero hAne hdz 1,
                  quadRoot_eq_of_disc_zero hAne hdz 2] at hy
              exact (lt_irrefl _) hy
            have hr2 := twoA_mul_quadRoot_add (B := B) (C := C) hAne 2
            simp only [if_neg (by decide : ¬(2 : Nat) = 1)] at hr2
            have hsp := Real.sqrt_pos_of_pos hd'
            exact Or.inr ⟨le_of_eq hp.symm, by linarith⟩
        · -- p > 0: pd > 0 (else y ≤ r₁)
          refine Or.inr ⟨le_of_lt hp, ?_⟩
          by_contra hpd0
          push_neg at hpd0
          have := (le_quadRoot1_iff hA hd y).mpr ⟨le_of_lt hp, hpd0⟩
          linarith
      · intro h
        rcases h with hp | ⟨hp1, hp2⟩
        · have hd' : 0 < B^2 - 4*A*C := by
            have := (quad_neg_iff_pos_lead hA B C y).mp hp
            have := sq_nonneg (2 * A * y + B)
            linarith
          exact (between_roots hA hd' hp).1
        · rcases eq_or_lt_of_le hp1 with hp | hp
          · -- p = 0, pd > 0: y = r₂ ≥ r₁ (d = 0 is impossible: pd = 0)
            have hy2 := (eq_quadRoot2_iff hA hd hp.symm).mpr (le_of_lt hp2)
            rw [hy2]
            rcases eq_or_lt_of_le hd with hdz | hd'
            · have hpd0 := (quad_zero_disc_root_iff hAne hdz.symm y).mp hp.symm
              linarith
            · exact quadRoot_lt hA hd'
          · -- p > 0, pd > 0: y > r₂ ≥ r₁
            have hy2 := (quadRoot2_lt_iff hA hd y).mpr ⟨hp, hp2⟩
            linarith [hle]
    | le =>
      show (y ≤ quadRoot 1 A B C) ↔ (0 ≤ A * y^2 + B * y + C ∧ 2 * A * y + B ≤ 0)
      exact le_quadRoot1_iff hA hd y
    | ge =>
      show (quadRoot 1 A B C ≤ y) ↔
        (A * y^2 + B * y + C ≤ 0 ∨ (0 ≤ A * y^2 + B * y + C ∧ 0 ≤ 2 * A * y + B))
      constructor
      · intro hy
        rcases lt_trichotomy (A * y^2 + B * y + C) 0 with hp | hp | hp
        · exact Or.inl (le_of_lt hp)
        · -- p = 0: the first disjunct `p ≤ 0` holds directly
          exact Or.inl (le_of_eq hp)
        · -- p > 0: pd ≥ 0 (else y < r₁)
          refine Or.inr ⟨le_of_lt hp, ?_⟩
          by_contra hpd0
          push_neg at hpd0
          have := (lt_quadRoot1_iff hA hd y).mpr ⟨hp, hpd0⟩
          linarith
      · intro h
        rcases h with hp | ⟨hp1, hp2⟩
        · -- p ≤ 0: between (incl. roots) ⇒ r₁ ≤ y
          rcases eq_or_lt_of_le hp with hp | hp
          · have hroots : y = quadRoot 1 A B C ∨ y = quadRoot 2 A B C := by
              rcases le_or_lt (2 * A * y + B) 0 with hpd | hpd
              · exact Or.inl ((eq_quadRoot1_iff hA hd hp).mpr hpd)
              · exact Or.inr ((eq_quadRoot2_iff hA hd hp).mpr (le_of_lt hpd))
            rcases hroots with rfl | rfl
            · exact le_refl _
            · exact hle
          · have hd' : 0 < B^2 - 4*A*C := by
              have := (quad_neg_iff_pos_lead hA B C y).mp hp
              have := sq_nonneg (2 * A * y + B)
              linarith
            exact le_of_lt (between_roots hA hd' hp).1
        · -- (0 ≤ p, 0 ≤ pd): y ≥ r₁
          rcases eq_or_lt_of_le hp1 with hp | hp
          · -- p = 0: y ∈ {r₁, r₂} both ≥ r₁
            have hroots : y = quadRoot 1 A B C ∨ y = quadRoot 2 A B C := by
              rcases le_or_lt (2 * A * y + B) 0 with hpd | hpd
              · exact Or.inl ((eq_quadRoot1_iff hA hd hp.symm).mpr hpd)
              · exact Or.inr ((eq_quadRoot2_iff hA hd hp.symm).mpr (le_of_lt hpd))
            rcases hroots with rfl | rfl
            · exact le_refl _
            · exact hle
          · -- p > 0, pd ≥ 0: y ≥ r₂ ≥ r₁
            rcases eq_or_lt_of_le hp2 with hpd | hpd
            · -- pd = 0, p > 0: impossible
              exact absurd hp (not_pos_of_pderiv_eq_zero hA hd hpd.symm)
            · have hy2 := (quadRoot2_lt_iff hA hd y).mpr ⟨hp, hpd⟩
              linarith [hle]
  · cases k with
    | eq =>
      show (y = quadRoot 2 A B C) ↔ (A * y^2 + B * y + C = 0 ∧ 0 ≤ 2 * A * y + B)
      constructor
      · intro h
        refine ⟨?_, ?_⟩
        · rw [h]
          exact quadRoot_is_root hAne hd 2
        · have hr := twoA_mul_quadRoot_add (B := B) (C := C) hAne 2
          simp only [if_neg (by decide : ¬(2 : Nat) = 1)] at hr
          have := Real.sqrt_nonneg (B^2 - 4*A*C)
          rw [h, hr]
          linarith
      · intro ⟨hp, hpd⟩
        exact (eq_quadRoot2_iff hA hd hp).mpr hpd
    | lt =>
      show (y < quadRoot 2 A B C) ↔
        (A * y^2 + B * y + C < 0 ∨ (0 ≤ A * y^2 + B * y + C ∧ 2 * A * y + B < 0))
      constructor
      · intro hy
        rcases lt_trichotomy (A * y^2 + B * y + C) 0 with hp | hp | hp
        · exact Or.inl hp
        · -- p = 0: y ∈ {r₁, r₂}; y < r₂ forces y = r₁ with pd < 0 (d > 0)
          have hroots : y = quadRoot 1 A B C ∨ y = quadRoot 2 A B C := by
            rcases le_or_lt (2 * A * y + B) 0 with hpd | hpd
            · exact Or.inl ((eq_quadRoot1_iff hA hd hp).mpr hpd)
            · exact Or.inr ((eq_quadRoot2_iff hA hd hp).mpr (le_of_lt hpd))
          rcases hroots with rfl | rfl
          · have hd' : 0 < B^2 - 4*A*C := by
              by_contra hc
              push_neg at hc
              have hdz : B^2 - 4*A*C = 0 := le_antisymm hc hd
              rw [quadRoot_eq_of_disc_zero hAne hdz 1,
                  quadRoot_eq_of_disc_zero hAne hdz 2] at hy
              exact (lt_irrefl _) hy
            have hr1 := twoA_mul_quadRoot_add (B := B) (C := C) hAne 1
            have hr1x : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by simpa using hr1
            have hsp := Real.sqrt_pos_of_pos hd'
            exact Or.inr ⟨le_of_eq hp.symm, by linarith⟩
          · exact absurd hy (lt_irrefl _)
        · -- p > 0: pd < 0 (else y ≥ r₂)
          refine Or.inr ⟨le_of_lt hp, ?_⟩
          by_contra hpd0
          push_neg at hpd0
          have := (le_quadRoot2_iff hA hd y).mpr ⟨le_of_lt hp, hpd0⟩
          linarith
      · intro h
        rcases h with hp | ⟨hp1, hp2⟩
        · have hd' : 0 < B^2 - 4*A*C := by
            have := (quad_neg_iff_pos_lead hA B C y).mp hp
            have := sq_nonneg (2 * A * y + B)
            linarith
          exact (between_roots hA hd' hp).2
        · rcases eq_or_lt_of_le hp1 with hp | hp
          · -- p = 0, pd < 0: y = r₁ < r₂ (d > 0; d = 0 impossible)
            have hy1 := (eq_quadRoot1_iff hA hd hp.symm).mpr (le_of_lt hp2)
            rw [hy1]
            rcases eq_or_lt_of_le hd with hdz | hd'
            · have hpd0 := (quad_zero_disc_root_iff hAne hdz.symm y).mp hp.symm
              linarith
            · exact quadRoot_lt hA hd'
          · -- p > 0, pd < 0: y < r₁ ≤ r₂
            have hy1 := (lt_quadRoot1_iff hA hd y).mpr ⟨hp, hp2⟩
            linarith [hle]
    | gt =>
      show (quadRoot 2 A B C < y) ↔ (0 < A * y^2 + B * y + C ∧ 0 < 2 * A * y + B)
      exact quadRoot2_lt_iff hA hd y
    | le =>
      show (y ≤ quadRoot 2 A B C) ↔
        (A * y^2 + B * y + C ≤ 0 ∨ (0 ≤ A * y^2 + B * y + C ∧ 2 * A * y + B ≤ 0))
      constructor
      · intro hy
        rcases lt_trichotomy (A * y^2 + B * y + C) 0 with hp | hp | hp
        · exact Or.inl (le_of_lt hp)
        · -- p = 0: the first disjunct `p ≤ 0` holds directly
          exact Or.inl (le_of_eq hp)
        · -- p > 0: pd ≤ 0 (else y > r₂)
          refine Or.inr ⟨le_of_lt hp, ?_⟩
          by_contra hpd0
          push_neg at hpd0
          have := (quadRoot2_lt_iff hA hd y).mpr ⟨hp, hpd0⟩
          linarith
      · intro h
        rcases h with hp | ⟨hp1, hp2⟩
        · -- p ≤ 0: y ≤ r₂
          rcases eq_or_lt_of_le hp with hp | hp
          · have hroots : y = quadRoot 1 A B C ∨ y = quadRoot 2 A B C := by
              rcases le_or_lt (2 * A * y + B) 0 with hpd | hpd
              · exact Or.inl ((eq_quadRoot1_iff hA hd hp).mpr hpd)
              · exact Or.inr ((eq_quadRoot2_iff hA hd hp).mpr (le_of_lt hpd))
            rcases hroots with rfl | rfl
            · exact hle
            · exact le_refl _
          · have hd' : 0 < B^2 - 4*A*C := by
              have := (quad_neg_iff_pos_lead hA B C y).mp hp
              have := sq_nonneg (2 * A * y + B)
              linarith
            exact le_of_lt (between_roots hA hd' hp).2
        · -- (0 ≤ p, 0 ≤ pd): y ≤ r₂
          rcases eq_or_lt_of_le hp1 with hp | hp
          · -- p = 0: y ∈ {r₁, r₂} both ≤ r₂
            have hroots : y = quadRoot 1 A B C ∨ y = quadRoot 2 A B C := by
              rcases le_or_lt (2 * A * y + B) 0 with hpd | hpd
              · exact Or.inl ((eq_quadRoot1_iff hA hd hp.symm).mpr hpd)
              · exact Or.inr ((eq_quadRoot2_iff hA hd hp.symm).mpr (le_of_lt hpd))
            rcases hroots with rfl | rfl
            · exact hle
            · exact le_refl _
          · -- p > 0, pd ≤ 0: y ≤ r₁ ≤ r₂
            rcases eq_or_lt_of_le hp2 with hpd | hpd
            · -- pd = 0, p > 0: impossible
              exact absurd hp (not_pos_of_pderiv_eq_zero hA hd hpd)
            · have hy1 := (lt_quadRoot1_iff hA hd y).mpr ⟨hp, hpd⟩
              linarith [hle]
    | ge =>
      show (quadRoot 2 A B C ≤ y) ↔ (0 ≤ A * y^2 + B * y + C ∧ 0 ≤ 2 * A * y + B)
      exact le_quadRoot2_iff hA hd y

/-- The Thom discharge (z3 `mk_quadratic_root` :787-820): the sign
literals on {disc, A, 2Ay+B, p} encode the root atom — the comparison
`ρ y ⋈_k root_i(p)` holds iff the region formula does. (The formula's
truth is evaluated by the composition from the `p`/`pDiff` sign facts;
the `sq = 0` case needs no `p` fact — definite-disc makes `p ≥ 0`
everywhere, exactly why z3 skips that `ensure_sign`.) -/
theorem thom_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
    (sq sa : Int)
    (hdeg : p.degreeIn y = 2) (hi : i = 1 ∨ i = 2)
    (hcan : MPoly.Canon p)
    (hsa : sa ≠ 0) (hAm : signMatches sa (evalP ρ ((coeffsOf p y)[2]!)))
    (hsq : sq = 0 ∨ sq = 1)
    (hdm : signMatches sq
      (evalP ρ ((coeffsOf p y)[1]!) ^ 2 -
        4 * evalP ρ ((coeffsOf p y)[2]!) * evalP ρ ((coeffsOf p y)[0]!))) :
    rootCmp k (ρ y) (quadRootVal i
      (evalP ρ ((coeffsOf p y)[2]!)) (evalP ρ ((coeffsOf p y)[1]!))
      (evalP ρ ((coeffsOf p y)[0]!))) ↔
      thomFormula k i
        (leadSgn (evalP ρ ((coeffsOf p y)[2]!)) * evalP ρ p)
        (leadSgn (evalP ρ ((coeffsOf p y)[2]!)) *
          (2 * evalP ρ ((coeffsOf p y)[2]!) * ρ y + evalP ρ ((coeffsOf p y)[1]!))) := by
  have hform := evalP_quadratic_form ρ y p hdeg hcan
  set Aρ := evalP ρ ((coeffsOf p y)[2]!)
  set Bρ := evalP ρ ((coeffsOf p y)[1]!)
  set Cρ := evalP ρ ((coeffsOf p y)[0]!)
  have hAne : Aρ ≠ 0 := hAm.ne_zero hsa
  have hd_nn : 0 ≤ Bρ^2 - 4 * Aρ * Cρ := hdm.nonneg hsq
  set s := leadSgn Aρ
  have hs2 : s^2 = 1 := leadSgn_sq Aρ
  have hsA : 0 < s * Aρ := leadSgn_mul_self_pos hAne
  have hdisc' : 0 ≤ (s * Bρ)^2 - 4 * (s * Aρ) * (s * Cρ) := by
    have e : (s * Bρ)^2 - 4 * (s * Aρ) * (s * Cρ) = s^2 * (Bρ^2 - 4 * Aρ * Cρ) := by
      ring
    rw [e, hs2, one_mul]
    exact hd_nn
  have hmain := thom_iff hsA hdisc' hi k (ρ y)
  have e1 : (s * Aρ) * (ρ y)^2 + (s * Bρ) * (ρ y) + (s * Cρ) = s * evalP ρ p := by
    rw [hform]
    ring
  have e2 : 2 * (s * Aρ) * (ρ y) + (s * Bρ) = s * (2 * Aρ * (ρ y) + Bρ) := by
    ring
  rw [e1, e2] at hmain
  have hval : quadRootVal i Aρ Bρ Cρ = quadRoot i (s * Aρ) (s * Bρ) (s * Cρ) := by
    unfold quadRootVal
    rfl
  rw [hval]
  exact hmain


/-! ## Reconstruction bridges: `discPolyOf` / `pDiffPolyOf` (+ normalize
sign-transfer)

The checker reconstructs the Thom polys from the payload `p` and matches
them BY VALUE against the clause's sign literals (F4). These lemmas feed
the sign facts at the eval level the discharges consume. -/

theorem Monomial.canon_erase {m : Monomial} (h : Monomial.Canon m) (y : Var) :
    Monomial.Canon (m.erase y) := by
  obtain ⟨hp, he⟩ := h
  exact ⟨hp.filter _, fun p hp' => he p (List.mem_of_mem_filter hp')⟩

theorem MPoly.canon_singleton {a : Int} {m : Monomial} (ha : a ≠ 0)
    (hm : Monomial.Canon m) : MPoly.Canon [(a, m)] := by
  constructor
  · exact List.pairwise_singleton _ _
  · intro t ht
    rw [List.mem_singleton] at ht
    rw [ht]
    exact ⟨ha, hm⟩

theorem mem_set_elim {α : Type*} (l : List α) (i : Nat) (v c : α)
    (hc : c ∈ l.set i v) : c = v ∨ c ∈ l := by
  by_cases hi : i < l.length
  · revert hc hi
    induction l generalizing i with
    | nil => intro hc hi; simp at hi
    | cons x l ih =>
      intro hc hi
      cases i with
      | zero =>
        have h0 : (x :: l).set 0 v = v :: l := rfl
        rw [h0, List.mem_cons] at hc
        exact hc.elim Or.inl (fun h => Or.inr (List.mem_cons_of_mem _ h))
      | succ i =>
        have hs : (x :: l).set (i + 1) v = x :: l.set i v := rfl
        rw [hs, List.mem_cons] at hc
        cases hc with
        | inl h => exact Or.inr (h ▸ List.mem_cons_self)
        | inr h =>
          have hi' : i < l.length := by
            have hh : (x :: l).length = l.length + 1 := rfl
            omega
          exact (ih i h hi').elim Or.inl (fun hh => Or.inr (List.mem_cons_of_mem _ hh))
  · rw [List.set_eq_of_length_le (Nat.le_of_not_lt hi)] at hc
    exact Or.inr hc

theorem coeffsOf_canon (p : MPoly) (y : Var) (hcan : MPoly.Canon p) :
    ∀ c ∈ coeffsOf p y, MPoly.Canon c := by
  have step : ∀ (init : List MPoly) (a : Int) (m : Monomial),
      (∀ c ∈ init, MPoly.Canon c) → a ≠ 0 → Monomial.Canon m →
      (∀ c ∈ init.set (m.degreeIn y) (MPoly.add init[m.degreeIn y]! [(a, m.erase y)]),
        MPoly.Canon c) := by
    intro init a m hinit ha hm c hc
    rcases mem_set_elim init _ _ c hc with rfl | hin
    · by_cases hi : m.degreeIn y < init.length
      · have hmem : init[m.degreeIn y]! ∈ init := by
          rw [getElem!_pos init _ hi]
          exact List.getElem_mem hi
        exact MPoly.add_canon (hinit _ hmem)
          (MPoly.canon_singleton ha (Monomial.canon_erase hm y))
      · have hset : init.set (m.degreeIn y)
            (MPoly.add init[m.degreeIn y]! [(a, m.erase y)]) = init :=
          List.set_eq_of_length_le (Nat.le_of_not_lt hi)
        rw [hset] at hc
        exact hinit _ hc
    · exact hinit c hin
  have go : ∀ (ts : MPoly) (init : List MPoly),
      (∀ c ∈ init, MPoly.Canon c) → (∀ t ∈ ts, t.1 ≠ 0 ∧ Monomial.Canon t.2) →
      ∀ c ∈ coeffsOf.go y init ts, MPoly.Canon c := by
    intro ts
    induction ts with
    | nil => intro init h _ c hc; exact h c hc
    | cons t ts ih =>
      obtain ⟨a, m⟩ := t
      intro init hinit hts c hc
      apply ih _ _ _ c hc
      · intro c' hc'
        exact step init a m hinit (hts (a, m) List.mem_cons_self).1
          (hts (a, m) List.mem_cons_self).2 c' hc'
      · intro t' ht'
        exact hts t' (List.mem_cons_of_mem _ ht')
  intro c hc
  unfold coeffsOf at hc
  exact go p _ (by
    intro c' hc'
    rw [List.mem_replicate] at hc'
    rw [hc'.2]
    exact MPoly.canon_nil) hcan.2 c hc

/-! ### The integer-content lemmas behind `managerNormalize`'s sign
transfer (it divides by the nonneg gcd `ic`; signs scale by a positive
factor, `MPolyOps.lean`/`MPolyZp.lean` mechanism) -/

theorem MPoly.ic_dvd (p : MPoly) : ∀ t ∈ p, p.ic ∣ t.1 := by
  have key : ∀ (l : MPoly) (acc : Int),
      (l.foldl (fun acc (b, _) => if acc == 1 then acc else (Int.gcd acc b : Int)) acc) ∣ acc ∧
      ∀ t ∈ l,
        (l.foldl (fun acc (b, _) => if acc == 1 then acc else (Int.gcd acc b : Int)) acc) ∣ t.1 := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons u l ih =>
      obtain ⟨b0, n0⟩ := u
      intro acc
      have ih' := ih (if acc == 1 then acc else (Int.gcd acc b0 : Int))
      have hstep_acc : (if acc == 1 then acc else (Int.gcd acc b0 : Int)) ∣ acc := by
        by_cases h : acc == 1
        · rw [if_pos h]
        · rw [if_neg h]; exact Int.gcd_dvd_left acc b0
      have hstep_b : (if acc == 1 then acc else (Int.gcd acc b0 : Int)) ∣ b0 := by
        by_cases h : acc == 1
        · have h1 : acc = 1 := beq_iff_eq.mp h
          rw [if_pos h, h1]
          exact one_dvd b0
        · rw [if_neg h]; exact Int.gcd_dvd_right acc b0
      rw [List.foldl_cons]
      show (List.foldl (fun acc (b, _) => if acc == 1 then acc else (Int.gcd acc b : Int))
            (if acc == 1 then acc else (Int.gcd acc b0 : Int)) l ∣ acc) ∧
        ∀ t ∈ (b0, n0) :: l, (List.foldl (fun acc (b, _) =>
            if acc == 1 then acc else (Int.gcd acc b : Int))
            (if acc == 1 then acc else (Int.gcd acc b0 : Int)) l) ∣ t.1
      constructor
      · exact ih'.1.trans hstep_acc
      · intro t ht
        obtain ⟨b, m⟩ := t
        cases List.mem_cons.mp ht with
        | inl heq =>
          rw [heq]
          exact ih'.1.trans hstep_b
        | inr hmem =>
          exact ih'.2 (b, m) hmem
  cases p with
  | nil => intro t h; simp at h
  | cons t rest =>
    obtain ⟨a0, m0⟩ := t
    intro t h
    obtain ⟨a, m⟩ := t
    rw [MPoly.ic]
    cases List.mem_cons.mp h with
    | inl heq =>
      rw [heq]
      exact (key rest _).1.trans (Int.gcd_dvd_right 0 a0)
    | inr hmem =>
      exact (key rest _).2 (a, m) hmem

theorem MPoly.ic_pos (p : MPoly) (hn : p ≠ []) (hc : ∀ t ∈ p, t.1 ≠ 0) : 0 < p.ic := by
  have hnn : 0 ≤ p.ic := by
    have key : ∀ (l : MPoly) (acc : Int), 0 ≤ acc →
        0 ≤ l.foldl (fun acc (b, _) => if acc == 1 then acc else (Int.gcd acc b : Int)) acc := by
      intro l
      induction l with
      | nil => intro acc h; exact h
      | cons u l ih =>
        obtain ⟨b0, n0⟩ := u
        intro acc hacc
        rw [List.foldl_cons]
        apply ih
        show 0 ≤ (if acc == 1 then acc else (Int.gcd acc b0 : Int))
        by_cases h : acc == 1
        · rw [if_pos h]; exact hacc
        · rw [if_neg h]; exact Int.natCast_nonneg _
    cases p with
    | nil => simp [MPoly.ic]
    | cons t rest =>
      obtain ⟨a0, m0⟩ := t
      rw [MPoly.ic]
      exact key rest _ (Int.natCast_nonneg _)
  cases p with
  | nil => exact absurd rfl hn
  | cons t rest =>
    obtain ⟨a0, m0⟩ := t
    have hd : MPoly.ic ((a0, m0) :: rest) ∣ a0 := MPoly.ic_dvd _ _ List.mem_cons_self
    have ha0 : a0 ≠ 0 := hc (a0, m0) List.mem_cons_self
    have hne : MPoly.ic ((a0, m0) :: rest) ≠ 0 := by
      intro h0
      rw [h0] at hd
      exact ha0 (eq_zero_of_zero_dvd hd)
    exact lt_of_le_of_ne hnn (Ne.symm hne)

theorem evalP_map_div (ρ : Nat → ℝ) {g : Int} (hg : 0 < g) (p : MPoly)
    (hd : ∀ t ∈ p, g ∣ t.1) :
    evalP ρ (p.map fun (a, m) => (a / g, m)) = evalP ρ p / g := by
  induction p with
  | nil => simp [evalP]
  | cons t p ih =>
    obtain ⟨a, m⟩ := t
    have ha : g ∣ a := hd (a, m) List.mem_cons_self
    have hd' : ∀ t ∈ p, g ∣ t.1 := fun x hx => hd x (List.mem_cons_of_mem _ hx)
    rw [List.map_cons, evalP, ih hd', evalP]
    obtain ⟨k, hk⟩ := ha
    have hg' : (g : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hg
    rw [hk, mul_comm g k, Int.mul_ediv_cancel _ (ne_of_gt hg)]
    push_cast
    field_simp

theorem signMatches_div_pos {s : Int} {v : ℝ} {g : Int} (hg : 0 < g) :
    signMatches s (v / (g : ℝ)) ↔ signMatches s v := by
  have hg' : (0 : ℝ) < g := by exact_mod_cast hg
  have e1 : v / (g : ℝ) < 0 ↔ v < 0 := by rw [div_lt_iff₀ hg', zero_mul]
  have e2 : v / (g : ℝ) = 0 ↔ v = 0 := by
    rw [div_eq_zero_iff]
    simp [show ((g : ℝ) ≠ 0) from ne_of_gt hg']
  have e3 : 0 < v / (g : ℝ) ↔ 0 < v := by rw [lt_div_iff₀ hg', zero_mul]
  unfold signMatches
  rw [e1, e2, e3]

theorem managerNormalize_none_eq (q : MPoly) (hq : q ≠ []) :
    MPoly.managerNormalize none q =
      if q.ic == 1 then q else q.map fun (a, m) => (a / q.ic, m) := by
  unfold MPoly.managerNormalize
  cases q with
  | nil => exact absurd rfl hq
  | cons t q => rfl

theorem signMatches_managerNormalize (ρ : Nat → ℝ) (s : Int) (q : MPoly)
    (hc : ∀ t ∈ q, t.1 ≠ 0) :
    signMatches s (evalP ρ (MPoly.managerNormalize none q)) ↔ signMatches s (evalP ρ q) := by
  by_cases hq : q = []
  · subst hq
    simp [MPoly.managerNormalize, evalP]
  · rw [managerNormalize_none_eq q hq]
    by_cases hg : q.ic == 1
    · rw [if_pos hg]
    · rw [if_neg hg]
      have hpos : 0 < q.ic := MPoly.ic_pos q hq hc
      rw [evalP_map_div ρ hpos q (MPoly.ic_dvd q)]
      exact signMatches_div_pos hpos

/-! ### The reconstructed Thom polys and their evals -/

theorem evalP_sub (ρ : Nat → ℝ) (p q : MPoly) :
    evalP ρ (MPoly.sub p q) = evalP ρ p - evalP ρ q := by
  rw [MPoly.sub, evalP_add, evalP_neg, sub_eq_add_neg]

/-- Checker-side reconstruction of `mk_quadratic_root`'s discriminant
poly (`B² − 4AC`; emission builds it from `coeffsIn`, we use `coeffsOf`
— BY-VALUE agreement is pinned in CheckTests). -/
def discPolyOf (p : MPoly) (y : Var) : MPoly :=
  let cs := coeffsOf p y
  (cs[1]!.mul cs[1]!).sub ((MPoly.ofInt 4).mul (cs[2]!.mul cs[0]!))

theorem evalP_discPolyOf (ρ : Nat → ℝ) (y : Var) (p : MPoly) :
    evalP ρ (discPolyOf p y) =
      evalP ρ ((coeffsOf p y)[1]!) ^ 2 -
        4 * evalP ρ ((coeffsOf p y)[2]!) * evalP ρ ((coeffsOf p y)[0]!) := by
  simp only [discPolyOf, evalP_sub, evalP_mul, evalP_ofInt]
  ring

/-- Checker-side reconstruction of `mk_quadratic_root`'s derivative poly
(`2Ay + B`, through the same `managerNormalize` content-strip as the
emission). -/
def pDiffPolyOf (p : MPoly) (y : Var) : MPoly :=
  let cs := coeffsOf p y
  MPoly.managerNormalize none
    (MPoly.add (MPoly.mul (MPoly.smulTerm 2 [] (cs[2]!)) (MPoly.ofVar y)) (cs[1]!))

theorem evalP_pDiffPolyOf_sign (ρ : Nat → ℝ) (y : Var) (p : MPoly) (s : Int)
    (hdeg : p.degreeIn y = 2) (hcan : MPoly.Canon p) :
    signMatches s (evalP ρ (pDiffPolyOf p y)) ↔
      signMatches s (2 * evalP ρ ((coeffsOf p y)[2]!) * ρ y +
        evalP ρ ((coeffsOf p y)[1]!)) := by
  have hlen : (coeffsOf p y).length = 3 := by rw [coeffsOf_length, hdeg]
  have hmemA : (coeffsOf p y)[2]! ∈ coeffsOf p y := by
    rw [getElem!_pos _ 2 (by rw [hlen]; decide)]
    exact List.getElem_mem (by rw [hlen]; decide)
  have hmemB : (coeffsOf p y)[1]! ∈ coeffsOf p y := by
    rw [getElem!_pos _ 1 (by rw [hlen]; decide)]
    exact List.getElem_mem (by rw [hlen]; decide)
  have hcA := coeffsOf_canon p y hcan _ hmemA
  have hcB := coeffsOf_canon p y hcan _ hmemB
  have hcq : MPoly.Canon (MPoly.add
      (MPoly.mul (MPoly.smulTerm 2 [] ((coeffsOf p y)[2]!)) (MPoly.ofVar y))
      ((coeffsOf p y)[1]!)) :=
    MPoly.add_canon
      (MPoly.mul_canon (MPoly.smulTerm_canon Monomial.canon_nil hcA)
        (MPoly.ofVar_canon y))
      hcB
  have hcs : ∀ t ∈ (MPoly.add
      (MPoly.mul (MPoly.smulTerm 2 [] ((coeffsOf p y)[2]!)) (MPoly.ofVar y))
      ((coeffsOf p y)[1]!)), t.1 ≠ 0 :=
    fun t ht => (hcq.2 t ht).1
  have hev : evalP ρ (MPoly.add
      (MPoly.mul (MPoly.smulTerm 2 [] ((coeffsOf p y)[2]!)) (MPoly.ofVar y))
      ((coeffsOf p y)[1]!)) =
      2 * evalP ρ ((coeffsOf p y)[2]!) * ρ y + evalP ρ ((coeffsOf p y)[1]!) := by
    rw [evalP_add, evalP_mul, evalP_smulTerm, evalP_ofVar]
    simp [evalM]
  rw [show pDiffPolyOf p y = MPoly.managerNormalize none (MPoly.add
      (MPoly.mul (MPoly.smulTerm 2 [] ((coeffsOf p y)[2]!)) (MPoly.ofVar y))
      ((coeffsOf p y)[1]!)) from rfl]
  rw [signMatches_managerNormalize ρ s _ hcs, hev]


/-! ## The cellBound discharge

By the two-step emission design (Trace.lean header), every cellBound
step follows its ENCODING step (linearRoot / thomQuadratic / rootGeneric
— and `addRootLiteral` is only ever called from `addCellLits`). The
mathematical content is entirely in the encoding discharges; the
cellBound wrappers here repackage them at the `rootVal` level: the
encoding step's iff + the sign facts (from the emitted literals
failing) + the formula's truth give the ordering fact the composition
collects. -/

theorem rootVal_eq_linear (ρ : Nat → ℝ) (y : Var) (i : Nat) (p : MPoly)
    (hdeg : p.degreeIn y = 1) :
    rootVal ρ y i p =
      -evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!) := by
  unfold rootVal
  rw [if_pos hdeg]

theorem rootVal_eq_quad (ρ : Nat → ℝ) (y : Var) (i : Nat) (p : MPoly)
    (hdeg : p.degreeIn y = 2) (hA : evalP ρ ((coeffsOf p y)[2]!) ≠ 0) :
    rootVal ρ y i p =
      quadRootVal i (evalP ρ ((coeffsOf p y)[2]!)) (evalP ρ ((coeffsOf p y)[1]!))
        (evalP ρ ((coeffsOf p y)[0]!)) := by
  unfold rootVal
  rw [if_neg (by rw [hdeg]; decide), if_pos hA]

/-- cellBound over a linear encoding: the ordering is the
`linearRoot_discharge` conclusion itself (the discharged literal's
failure IS the root comparison). -/
theorem cellBound_linear (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p : MPoly) (mkNeg : Bool)
    (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (hAq : (0 : ℝ) < (if mkNeg then (-1 : ℝ) else 1) * evalP ρ ((coeffsOf p y)[1]!))
    (hfails : ¬ SHolds ρ (linearRootEmitted k p mkNeg).1
      (linearRootEmitted k p mkNeg).2) :
    rootCmp k (ρ y) (rootVal ρ y i p) := by
  rw [rootVal_eq_linear ρ y i p hdeg]
  exact (linearRoot_discharge ρ k y p mkNeg hdeg hcan hAq).mp hfails

/-- cellBound over a Thom encoding: the encoding iff + the region
formula's truth (from the sign facts) give the ordering. -/
theorem cellBound_thom (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p : MPoly) (sq sa : Int)
    (hdeg : p.degreeIn y = 2) (hi : i = 1 ∨ i = 2)
    (hcan : MPoly.Canon p)
    (hsa : sa ≠ 0) (hAm : signMatches sa (evalP ρ ((coeffsOf p y)[2]!)))
    (hsq : sq = 0 ∨ sq = 1)
    (hdm : signMatches sq
      (evalP ρ ((coeffsOf p y)[1]!) ^ 2 -
        4 * evalP ρ ((coeffsOf p y)[2]!) * evalP ρ ((coeffsOf p y)[0]!)))
    (hform : thomFormula k i
      (leadSgn (evalP ρ ((coeffsOf p y)[2]!)) * evalP ρ p)
      (leadSgn (evalP ρ ((coeffsOf p y)[2]!)) *
        (2 * evalP ρ ((coeffsOf p y)[2]!) * ρ y + evalP ρ ((coeffsOf p y)[1]!)))) :
    rootCmp k (ρ y) (rootVal ρ y i p) := by
  rw [rootVal_eq_quad ρ y i p hdeg (hAm.ne_zero hsa)]
  exact (thom_discharge ρ k y i p sq sa hdeg hi hcan hsa hAm hsq hdm).mpr hform


/-- `rootGeneric` discharge: the step's clause literal (`¬atom`)
failing unfolds to root count + comparison — definitional, but the
fragment content (deg ≤ 2 ⇒ first-order) is what makes it checkable. -/
theorem rootGeneric_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat)
    (p : MPoly) :
    (¬ ALitHolds ρ (.root ⟨k, y, i, p⟩) true) ↔
      (i ≤ rootCount ρ y p ∧ rootCmp k (ρ y) (rootVal ρ y i p)) := by
  show (¬ ¬ RootAtom.Holds ρ ⟨k, y, i, p⟩) ↔ _
  rw [not_not]
  exact Iff.rfl

/-- Deg-1 with vanishing lead ⇒ no roots (the constant-in-`y` case of
the definite-disc family, G4 census). -/
theorem rootCount_zero_of_deg1_lc_zero (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 1) (hA : evalP ρ ((coeffsOf p y)[1]!) = 0) :
    rootCount ρ y p = 0 := by
  unfold rootCount
  rw [if_pos hdeg, if_neg (fun h => h hA)]

/-- One-le-rootCount forces a nonvanishing lead at deg-1 (the deg-1
count if-cascade, G11 lane antecedent). -/
theorem ne_of_one_le_rootCount_deg1 (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 1) (h : 1 ≤ rootCount ρ y p) :
    evalP ρ ((coeffsOf p y)[1]!) ≠ 0 := by
  intro hn
  rw [rootCount_zero_of_deg1_lc_zero ρ y p hdeg hn] at h
  exact absurd h (by decide)

/-- G11 uniform identity: for deg-1 with a nonvanishing lead, the
linear root comparison is equivalent to the sign-matched full-poly
comparison, with `S·A > 0` choosing which side of `0` the scaled poly
lands on — both lead signs collapse into one form (the comparison
flip and the multiplication by the same-sign `S` cancel in the
`S·A > 0` denominator). z3's `mk_linear_root` encoding is the
sign-conditional special case of this identity (:861-878, kind-remap +
`mk_neg`); this is the uniform form consumed by the production
`rootGeneric` (non-encoded, vanishing-lc) lane — see
`linearRootNonconst{Pos,Neg}_discharge`. -/
theorem linearNonconst_aux (ρ : Nat → ℝ) (k : RootKind) (y : Var) (p : MPoly)
    (S : ℝ) (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (hSA : (0 : ℝ) < S * evalP ρ ((coeffsOf p y)[1]!)) :
    rootCmp k (ρ y) (rootVal ρ y 1 p) ↔
      rootCmp k (S * evalP ρ p) 0 := by
  have hA : evalP ρ ((coeffsOf p y)[1]!) ≠ 0 := fun h => by
    rw [h] at hSA; simp at hSA
  have hS : S ≠ 0 := fun h => by rw [h] at hSA; simp at hSA
  rw [rootVal_eq_linear ρ y 1 p hdeg, evalP_linear_form ρ y p hdeg hcan]
  have hD : (0 : ℝ) < S * evalP ρ ((coeffsOf p y)[1]!) := hSA
  have hDn : S * evalP ρ ((coeffsOf p y)[1]!) ≠ 0 := ne_of_gt hD
  have hrw : -evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!) =
      -(evalP ρ ((coeffsOf p y)[0]!) * S) /
        (S * evalP ρ ((coeffsOf p y)[1]!)) := by
    field_simp [hS, hA, hDn]
  rw [hrw]
  cases k
  · simp only [rootCmp]
    rw [eq_div_iff hDn]
    constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith
  · simp only [rootCmp]
    rw [lt_div_iff₀ hD]
    constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith
  · simp only [rootCmp]
    rw [div_lt_iff₀ hD]
    constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith
  · simp only [rootCmp]
    rw [le_div_iff₀ hD]
    constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith
  · simp only [rootCmp]
    rw [div_le_iff₀ hD]
    constructor <;> intro h <;> ring_nf at h ⊢ <;> linarith

/-- The positive-lead instance of the `rootGeneric` deg-1 uniform
identity (G11). -/
theorem linearRootNonconstPos_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var)
    (p : MPoly) (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (_hholds : 1 ≤ rootCount ρ y p)
    (hApos : (0 : ℝ) < evalP ρ ((coeffsOf p y)[1]!)) :
    rootCmp k (ρ y) (rootVal ρ y 1 p) ↔ rootCmp k (evalP ρ p) 0 := by
  have h := linearNonconst_aux ρ k y p (1 : ℝ) hdeg hcan (by
    simpa [one_mul] using hApos)
  simpa [one_mul] using h

/-- The negative-lead instance (G11). -/
theorem linearRootNonconstNeg_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var)
    (p : MPoly) (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (_hholds : 1 ≤ rootCount ρ y p)
    (hAneg : evalP ρ ((coeffsOf p y)[1]!) < (0 : ℝ)) :
    rootCmp k (ρ y) (rootVal ρ y 1 p) ↔ rootCmp k (-evalP ρ p) 0 := by
  have h := linearNonconst_aux ρ k y p (-1 : ℝ) hdeg hcan (by
    have : (0 : ℝ) < -evalP ρ ((coeffsOf p y)[1]!) := neg_pos.mpr hAneg
    simpa [neg_one_mul] using this)
  simpa [neg_one_mul] using h

/-- The two-sign disjunction form (G11): without a clause sign fact for
the lead, the root comparison yields a sign-conditional disjunction
the Or-splitting glue consumes. -/
theorem linearRootNonconst_disjunction (ρ : Nat → ℝ) (k : RootKind) (y : Var)
    (p : MPoly) (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (hholds : 1 ≤ rootCount ρ y p) :
    rootCmp k (ρ y) (rootVal ρ y 1 p) →
      ((0 : ℝ) < evalP ρ ((coeffsOf p y)[1]!) ∧ rootCmp k (evalP ρ p) 0) ∨
      (evalP ρ ((coeffsOf p y)[1]!) < (0 : ℝ) ∧ rootCmp k (-evalP ρ p) 0) := by
  intro h
  have hAnz := ne_of_one_le_rootCount_deg1 ρ y p hdeg hholds
  rcases lt_trichotomy (evalP ρ ((coeffsOf p y)[1]!)) 0 with hA | hA | hA
  · exact Or.inr ⟨hA,
      (linearRootNonconstNeg_discharge ρ k y p hdeg hcan hholds hA).mp h⟩
  · exact absurd hA hAnz
  · exact Or.inl ⟨hA,
      (linearRootNonconstPos_discharge ρ k y p hdeg hcan hholds hA).mp h⟩

/-- Deg-1 with nonvanishing lead ⇒ exactly one root (the other side
of `rootCount_zero_of_deg1_lc_zero`). -/
theorem rootCount_one_of_deg1_lc_ne (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 1) (hA : evalP ρ ((coeffsOf p y)[1]!) ≠ 0) :
    rootCount ρ y p = 1 := by
  unfold rootCount
  rw [if_pos hdeg, if_pos hA]

/-- The negated-`Holds` disjunction at deg 1 (G11's negative side):
from the count if-form, `¬ Holds` splits into the vanishing-lead case
or the comparison failing — both plain glue facts, no deferred
discharge needed at split time. -/
theorem negHolds_deg1_disjunction (ρ : Nat → ℝ) (k : RootKind) (y : Var)
    (p : MPoly) (hdeg : p.degreeIn y = 1)
    (h : ¬ RootAtom.Holds ρ ⟨k, y, 1, p⟩) :
    evalP ρ ((coeffsOf p y)[1]!) = (0 : ℝ) ∨
      ¬ rootCmp k (ρ y) (rootVal ρ y 1 p) := by
  by_cases hc : (⟨k, y, 1, p⟩ : RootAtom).i ≤ rootCount ρ y p
  · exact Or.inr (fun hcmp => h ⟨hc, hcmp⟩)
  · exact Or.inl (by
      by_contra hA
      exact hc (le_of_eq (rootCount_one_of_deg1_lc_ne ρ y p hdeg hA).symm))

/-- The negative-side three-way (G11, close-out review F-ii): a `¬ Holds`
fact at deg 1 expands to the lead's trichotomy with the two sign
branches converted to first-order comparisons — the negative analogue
of `linearRootNonconst_disjunction`, needing no clause sign fact (z3
emits the deg-1 non-const-lc root atom with NO lc guard — `mk_linear_root`
fails its const check and `add_root_literal` adds the bare atom at
nlsat_explain.cpp:725-737 — so the sign is not structurally present). -/
theorem negHolds_deg1_trichotomy (ρ : Nat → ℝ) (k : RootKind) (y : Var)
    (p : MPoly) (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p)
    (h : ¬ RootAtom.Holds ρ ⟨k, y, 1, p⟩) :
    evalP ρ ((coeffsOf p y)[1]!) = (0 : ℝ) ∨
      ((0 : ℝ) < evalP ρ ((coeffsOf p y)[1]!) ∧ ¬ rootCmp k (evalP ρ p) 0) ∨
      (evalP ρ ((coeffsOf p y)[1]!) < (0 : ℝ) ∧ ¬ rootCmp k (-evalP ρ p) 0) := by
  rcases negHolds_deg1_disjunction ρ k y p hdeg h with hA | hcmp
  · exact Or.inl hA
  · rcases lt_trichotomy (evalP ρ ((coeffsOf p y)[1]!)) 0 with hA | hA | hA
    · exact Or.inr (Or.inr ⟨hA, by
        have hrc := rootCount_one_of_deg1_lc_ne ρ y p hdeg (ne_of_lt hA)
        exact (Iff.not (linearRootNonconstNeg_discharge ρ k y p hdeg hcan
          (le_of_eq hrc.symm) hA)).mp hcmp⟩)
    · exact Or.inl hA
    · exact Or.inr (Or.inl ⟨hA, by
        have hrc := rootCount_one_of_deg1_lc_ne ρ y p hdeg (ne_of_gt hA)
        exact (Iff.not (linearRootNonconstPos_discharge ρ k y p hdeg hcan
          (le_of_eq hrc.symm) hA)).mp hcmp⟩)


/-! ## 19b pseudoDivision — the sign-transfer family

From z3's own mathematical contract `lc^d · f = Q·eq + R` (the
pseudo-remainder identity, polynomial.cpp:5095 — re-proved per-instance
by `Refute.pseudoDivisionIdentity`, never trusted from the payload),
the factor's sign transfers by the parity of the exponent and the lc
sign — the :1132-1137 rule, cross-checked line-by-line: **d even ⟹
sign f = sign r** (the `d % 2 == 1` guard fails; pd6 witnessed); **d
odd ∧ lc > 0 ⟹ sign f = sign r** (`lc_sign < 0` fails; pd1/pd2/pd3
witnessed); **d odd ∧ lc < 0 ⟹ sign f = −sign r** (pd4 witnessed).
d-parity and lcSign are never trusted: the exponent and lc-sign are
hypotheses of each lemma (19b decision 1 — the perturbation
(d+1, lc·Q, lc·r) scales R and flips parity in cancellation, so any
identity witness yields the same conclusion). The const-remainder
path-(b) collapse (:1141-1157) is the `eq` shape with `R = 0` — no
separate lemma. -/

section PdSignTransfer

variable {L F Q E R : ℝ} {m : Nat}

/-- Under `E = 0` the pseudo-division identity collapses to the
multiplier form. -/
theorem pd_id_apply (hId : T * F = Q * E + R) (hE : E = 0) : T * F = R := by
  rw [hId, hE, mul_zero, zero_add]

theorem pdSign_even_gt (hL : L ≠ 0) (hE : E = 0)
    (hId : L ^ (2 * m) * F = Q * E + R) : 0 < F ↔ 0 < R := by
  have hT : 0 < L ^ (2 * m) := Even.pow_pos (even_two_mul m) hL
  rw [← pd_id_apply hId hE]; exact (mul_pos_iff_of_pos_left hT).symm

theorem pdSign_even_lt (hL : L ≠ 0) (hE : E = 0)
    (hId : L ^ (2 * m) * F = Q * E + R) : F < 0 ↔ R < 0 := by
  have hT : 0 < L ^ (2 * m) := Even.pow_pos (even_two_mul m) hL
  rw [← pd_id_apply hId hE, ← not_le, ← not_le, mul_nonneg_iff_of_pos_left hT]

theorem pdSign_even_ge (hL : L ≠ 0) (hE : E = 0)
    (hId : L ^ (2 * m) * F = Q * E + R) : 0 ≤ F ↔ 0 ≤ R := by
  have hT : 0 < L ^ (2 * m) := Even.pow_pos (even_two_mul m) hL
  rw [← pd_id_apply hId hE]; exact (mul_nonneg_iff_of_pos_left hT).symm

theorem pdSign_even_le (hL : L ≠ 0) (hE : E = 0)
    (hId : L ^ (2 * m) * F = Q * E + R) : F ≤ 0 ↔ R ≤ 0 := by
  have hT : 0 < L ^ (2 * m) := Even.pow_pos (even_two_mul m) hL
  rw [← pd_id_apply hId hE, ← not_lt, ← not_lt, mul_pos_iff_of_pos_left hT]

theorem pdSign_even_eq (hL : L ≠ 0) (hE : E = 0)
    (hId : L ^ (2 * m) * F = Q * E + R) : F = 0 ↔ R = 0 := by
  have hT : L ^ (2 * m) ≠ 0 := pow_ne_zero _ hL
  rw [← pd_id_apply hId hE]
  constructor
  · intro hF; rw [hF, mul_zero]
  · intro hTF
    rcases mul_eq_zero.mp hTF with hT0 | hF
    · exact absurd hT0 hT
    · exact hF

theorem pdSign_odd_pos_gt (hL : 0 < L) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : 0 < F ↔ 0 < R := by
  have hT : 0 < L ^ (2 * m + 1) := (Odd.pow_pos_iff (odd_two_mul_add_one m)).mpr hL
  rw [← pd_id_apply hId hE]; exact (mul_pos_iff_of_pos_left hT).symm

theorem pdSign_odd_pos_lt (hL : 0 < L) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : F < 0 ↔ R < 0 := by
  have hT : 0 < L ^ (2 * m + 1) := (Odd.pow_pos_iff (odd_two_mul_add_one m)).mpr hL
  rw [← pd_id_apply hId hE, ← not_le, ← not_le, mul_nonneg_iff_of_pos_left hT]

theorem pdSign_odd_pos_ge (hL : 0 < L) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : 0 ≤ F ↔ 0 ≤ R := by
  have hT : 0 < L ^ (2 * m + 1) := (Odd.pow_pos_iff (odd_two_mul_add_one m)).mpr hL
  rw [← pd_id_apply hId hE]; exact (mul_nonneg_iff_of_pos_left hT).symm

theorem pdSign_odd_pos_le (hL : 0 < L) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : F ≤ 0 ↔ R ≤ 0 := by
  have hT : 0 < L ^ (2 * m + 1) := (Odd.pow_pos_iff (odd_two_mul_add_one m)).mpr hL
  rw [← pd_id_apply hId hE, ← not_lt, ← not_lt, mul_pos_iff_of_pos_left hT]

theorem pdSign_odd_pos_eq (hL : 0 < L) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : F = 0 ↔ R = 0 := by
  have hT : L ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hL)
  rw [← pd_id_apply hId hE]
  constructor
  · intro hF; rw [hF, mul_zero]
  · intro hTF
    rcases mul_eq_zero.mp hTF with hT0 | hF
    · exact absurd hT0 hT
    · exact hF

theorem pdSign_odd_neg_gt (hL : L < 0) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : 0 < F ↔ R < 0 := by
  have hT : L ^ (2 * m + 1) < 0 := (Odd.pow_neg_iff (odd_two_mul_add_one m)).mpr hL
  have hS : 0 < - L ^ (2 * m + 1) := neg_pos.mpr hT
  rw [← pd_id_apply hId hE,
    show L ^ (2 * m + 1) * F = -((- L ^ (2 * m + 1)) * F) by ring,
    neg_lt_zero, mul_pos_iff_of_pos_left hS]

theorem pdSign_odd_neg_lt (hL : L < 0) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : F < 0 ↔ 0 < R := by
  have hT : L ^ (2 * m + 1) < 0 := (Odd.pow_neg_iff (odd_two_mul_add_one m)).mpr hL
  have hS : 0 < - L ^ (2 * m + 1) := neg_pos.mpr hT
  rw [← pd_id_apply hId hE,
    show L ^ (2 * m + 1) * F = -((- L ^ (2 * m + 1)) * F) by ring,
    neg_pos, ← not_le, ← not_le, mul_nonneg_iff_of_pos_left hS]

theorem pdSign_odd_neg_ge (hL : L < 0) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : 0 ≤ F ↔ R ≤ 0 := by
  have hT : L ^ (2 * m + 1) < 0 := (Odd.pow_neg_iff (odd_two_mul_add_one m)).mpr hL
  have hS : 0 < - L ^ (2 * m + 1) := neg_pos.mpr hT
  rw [← pd_id_apply hId hE,
    show L ^ (2 * m + 1) * F = -((- L ^ (2 * m + 1)) * F) by ring,
    neg_nonpos, mul_nonneg_iff_of_pos_left hS]

theorem pdSign_odd_neg_le (hL : L < 0) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : F ≤ 0 ↔ 0 ≤ R := by
  have hT : L ^ (2 * m + 1) < 0 := (Odd.pow_neg_iff (odd_two_mul_add_one m)).mpr hL
  have hS : 0 < - L ^ (2 * m + 1) := neg_pos.mpr hT
  rw [← pd_id_apply hId hE,
    show L ^ (2 * m + 1) * F = -((- L ^ (2 * m + 1)) * F) by ring,
    neg_nonneg, ← not_lt, ← not_lt, mul_pos_iff_of_pos_left hS]

theorem pdSign_odd_neg_eq (hL : L < 0) (hE : E = 0)
    (hId : L ^ (2 * m + 1) * F = Q * E + R) : F = 0 ↔ R = 0 := by
  have hT : L ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (ne_of_lt hL)
  rw [← pd_id_apply hId hE]
  constructor
  · intro hF; rw [hF, mul_zero]
  · intro hTF
    rcases mul_eq_zero.mp hTF with hT0 | hF
    · exact absurd hT0 hT
    · exact hF

end PdSignTransfer


/-- Deg-2 with both `A` and `B` vanishing ⇒ no roots (the
constant-in-`y` degenerate; `A = 0, B ≠ 0` counts 1). -/
theorem rootCount_zero_of_deg2_lc_zero (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 2) (hA : evalP ρ ((coeffsOf p y)[2]!) = 0)
    (hB : evalP ρ ((coeffsOf p y)[1]!) = 0) :
    rootCount ρ y p = 0 := by
  unfold rootCount
  rw [if_neg (by rw [hdeg]; decide), if_neg (fun h => h hA),
    if_neg (fun h => h hB)]

/-- Deg-2 negative disc ⇒ no roots ⇒ the atom is false. -/
theorem rootCount_zero_of_neg_disc (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 2)
    (hd : evalP ρ ((coeffsOf p y)[1]!)^2 -
      4 * evalP ρ ((coeffsOf p y)[2]!) * evalP ρ ((coeffsOf p y)[0]!) < 0) :
    rootCount ρ y p = 0 := by
  unfold rootCount
  rw [if_neg (by rw [hdeg]; decide)]
  set A := evalP ρ ((coeffsOf p y)[2]!)
  set B := evalP ρ ((coeffsOf p y)[1]!)
  set C := evalP ρ ((coeffsOf p y)[0]!)
  by_cases hA : A = 0
  · simp [hA]
    by_cases hB : B = 0
    · simp [hB]
    · simp only [hB, if_true]
      -- A = 0, B ≠ 0: count 1 — but disc = B² < 0 is impossible
      exfalso
      rw [hA] at hd
      simp at hd
      exact absurd hd (by have := sq_nonneg B; linarith)
  · rw [if_pos hA]
    split_ifs with h1 h2
    · rfl
    · exact h1 hd
    · exact h1 hd

/-- Index beyond the root count ⇒ the atom is false (z3 :435-437). -/
theorem rootAtom_false_of_index_lt (ρ : Nat → ℝ) (k : RootKind) (y : Var)
    (i : Nat) (p : MPoly) (hi : rootCount ρ y p < i) :
    ¬ RootAtom.Holds ρ ⟨k, y, i, p⟩ := by
  intro h
  obtain ⟨h1, _⟩ := h
  have hle : i ≤ rootCount ρ y p := h1
  omega

end Check

end LeanNonlinearArith.Nlsat
