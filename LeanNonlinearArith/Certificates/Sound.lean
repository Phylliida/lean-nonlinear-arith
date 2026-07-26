import Mathlib
import LeanNonlinearArith.Certificates.Defs
import LeanNonlinearArith.RootCounting.Spike

/-!
# nla-09 (trusted bridge, soundness) — certificate checkers are sound

Once-and-for-all theorems turning a kernel-`decide`d checker run into a
real-number fact:

* `checkNoRoot_sound`  — `evalZ cs` has no root on `[a, b]`;
* `checkUniqueRoot_sound` — exactly one root on `[a, b]`;
* `checkPosOn_sound` / `checkNegOn_sound` — strict sign on `[a, b]`.

The per-instance work is *entirely* in the `decide`; nothing here depends
on the particular polynomial or certificate. Structure: a reflection layer
(`evalZ` real semantics of coefficient lists: continuity, `HasDerivAt`
against `derivZ`, the `absZ` coefficient bound), a homomorphism layer
(`toR` semantics of unnormalized-pair arithmetic under positive
denominators), then the `lip` leaf via the mean value theorem
(`norm_image_sub_le_of_norm_deriv_le`) and the wrappers via IVT +
strict monotonicity + `sign_invariant_of_no_root` (nla-02).
-/

namespace LeanNonlinearArith.Certificates

open Set

/-- Real value of an unnormalized pair. -/
noncomputable def toR (x : PairQ) : ℝ := (x.1 : ℝ) / (x.2 : ℝ)

/-- Real Horner semantics of a ℤ-coefficient list (index = degree). -/
noncomputable def evalZ (cs : List Int) (x : ℝ) : ℝ :=
  cs.foldr (fun c acc => (c : ℝ) + x * acc) 0

/-! ## Reflection layer: `evalZ` -/

@[simp] theorem evalZ_nil (x : ℝ) : evalZ [] x = 0 := rfl

@[simp] theorem evalZ_cons (c : Int) (cs : List Int) (x : ℝ) :
    evalZ (c :: cs) x = (c : ℝ) + x * evalZ cs x := rfl

theorem evalZ_addZ (xs ys : List Int) (t : ℝ) :
    evalZ (addZ xs ys) t = evalZ xs t + evalZ ys t := by
  induction xs generalizing ys with
  | nil => simp [addZ]
  | cons x xs ih =>
    cases ys with
    | nil => simp [addZ]
    | cons y ys => simp [addZ, ih]; ring

theorem continuous_evalZ (cs : List Int) : Continuous (evalZ cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih =>
    have : evalZ (c :: cs) = fun x => (c : ℝ) + x * evalZ cs x := rfl
    rw [this]
    exact continuous_const.add (continuous_id.mul ih)

theorem hasDerivAt_evalZ (cs : List Int) (x : ℝ) :
    HasDerivAt (evalZ cs) (evalZ (derivZ cs) x) x := by
  induction cs with
  | nil => simpa [derivZ] using hasDerivAt_const x (0 : ℝ)
  | cons c cs ih =>
    have h1 : HasDerivAt (fun t : ℝ => t * evalZ cs t)
        (1 * evalZ cs x + x * evalZ (derivZ cs) x) x :=
      (hasDerivAt_id x).mul ih
    have h2 : HasDerivAt (evalZ (c :: cs))
        (1 * evalZ cs x + x * evalZ (derivZ cs) x) x := by
      have hfun : evalZ (c :: cs) = fun t => (c : ℝ) + t * evalZ cs t := rfl
      rw [hfun]
      exact h1.const_add (c : ℝ)
    have h3 : evalZ (derivZ (c :: cs)) x
        = 1 * evalZ cs x + x * evalZ (derivZ cs) x := by
      simp [derivZ, evalZ_addZ]
    rw [h3]
    exact h2

/-- The `absZ` polynomial at `M` dominates `|evalZ|` on `[-M, M]`. -/
theorem abs_evalZ_le {x M : ℝ} (h : |x| ≤ M) (cs : List Int) :
    |evalZ cs x| ≤ evalZ (absZ cs) M := by
  induction cs with
  | nil => simp [absZ]
  | cons c cs ih =>
    have hM : 0 ≤ M := (abs_nonneg x).trans h
    have habs : ((c.natAbs : Int) : ℝ) = |(c : ℝ)| := by push_cast; ring
    calc |evalZ (c :: cs) x|
        ≤ |(c : ℝ)| + |x * evalZ cs x| := by rw [evalZ_cons]; exact abs_add_le _ _
      _ = |(c : ℝ)| + |x| * |evalZ cs x| := by rw [abs_mul]
      _ ≤ |(c : ℝ)| + M * evalZ (absZ cs) M := by
          have := mul_le_mul h ih (abs_nonneg _) hM
          linarith
      _ = evalZ (absZ (c :: cs)) M := by
          simp only [absZ, List.map_cons, evalZ_cons, habs]

/-! ## Homomorphism layer: pair arithmetic under positive denominators -/

theorem den_cast_pos {x : PairQ} (hx : 0 < x.2) : (0 : ℝ) < (x.2 : ℝ) := by
  exact_mod_cast hx

theorem pAdd_den_pos {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (pAdd x y).2 := mul_pos hx hy

theorem pSub_den_pos {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (pSub x y).2 := mul_pos hx hy

theorem pMul_den_pos {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (pMul x y).2 := mul_pos hx hy

theorem pAbs_den_pos {x : PairQ} (hx : 0 < x.2) : 0 < (pAbs x).2 := hx

theorem pMid_den_pos {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (pMid x y).2 := by
  show (0 : Int) < 2 * (x.2 * y.2)
  positivity

theorem pHalf_den_pos {x : PairQ} (hx : 0 < x.2) : 0 < (pHalf x).2 := by
  show (0 : Int) < 2 * x.2
  positivity

theorem pMax_den_pos {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    0 < (pMax x y).2 := by
  unfold pMax; split <;> assumption

theorem evalP_den_pos (cs : List Int) {x : PairQ} (hx : 0 < x.2) :
    0 < (evalP cs x).2 := by
  induction cs with
  | nil => norm_num [evalP]
  | cons c cs ih =>
    have : evalP (c :: cs) x = pAdd (c, 1) (pMul x (evalP cs x)) := rfl
    rw [this]
    exact pAdd_den_pos (by norm_num) (pMul_den_pos hx ih)

theorem toR_pAdd {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    toR (pAdd x y) = toR x + toR y := by
  have hx' := (den_cast_pos hx).ne'
  have hy' := (den_cast_pos hy).ne'
  unfold toR pAdd
  push_cast
  field_simp

theorem toR_pSub {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    toR (pSub x y) = toR x - toR y := by
  have hx' := (den_cast_pos hx).ne'
  have hy' := (den_cast_pos hy).ne'
  unfold toR pSub
  push_cast
  field_simp

theorem toR_pMul {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    toR (pMul x y) = toR x * toR y := by
  have hx' := (den_cast_pos hx).ne'
  have hy' := (den_cast_pos hy).ne'
  unfold toR pMul
  push_cast
  field_simp

theorem toR_pAbs {x : PairQ} (hx : 0 < x.2) : toR (pAbs x) = |toR x| := by
  have habs : ((x.1.natAbs : Int) : ℝ) = |(x.1 : ℝ)| := by push_cast; ring
  unfold toR pAbs
  rw [abs_div, abs_of_pos (den_cast_pos hx), habs]

theorem toR_pMid {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    toR (pMid x y) = (toR x + toR y) / 2 := by
  have hx' := (den_cast_pos hx).ne'
  have hy' := (den_cast_pos hy).ne'
  unfold toR pMid
  push_cast
  field_simp

theorem toR_pHalf {x : PairQ} (hx : 0 < x.2) : toR (pHalf x) = toR x / 2 := by
  have hx' := (den_cast_pos hx).ne'
  unfold toR pHalf
  push_cast
  field_simp

theorem pLt_iff {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    pLt x y = true ↔ toR x < toR y := by
  unfold pLt toR
  rw [decide_eq_true_iff, div_lt_div_iff₀ (den_cast_pos hx) (den_cast_pos hy)]
  exact_mod_cast Iff.rfl

theorem pLe_iff {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    pLe x y = true ↔ toR x ≤ toR y := by
  unfold pLe toR
  rw [decide_eq_true_iff, div_le_div_iff₀ (den_cast_pos hx) (den_cast_pos hy)]
  exact_mod_cast Iff.rfl

theorem toR_pMax {x y : PairQ} (hx : 0 < x.2) (hy : 0 < y.2) :
    toR (pMax x y) = max (toR x) (toR y) := by
  unfold pMax
  rcases hxy : pLe x y with _ | _
  · have : ¬ toR x ≤ toR y := by
      rw [← pLe_iff hx hy, hxy]; simp
    simp [max_eq_left (le_of_not_ge this)]
  · have := (pLe_iff hx hy).mp hxy
    simp [max_eq_right this]

theorem toR_num_pos_iff {x : PairQ} (hx : 0 < x.2) : 0 < toR x ↔ 0 < x.1 := by
  unfold toR
  rw [div_pos_iff]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, hd⟩)
    · exact_mod_cast h
    · exact absurd (den_cast_pos hx) (not_lt.mpr hd.le)
  · intro h
    exact Or.inl ⟨by exact_mod_cast h, den_cast_pos hx⟩

theorem toR_num_neg_iff {x : PairQ} (hx : 0 < x.2) : toR x < 0 ↔ x.1 < 0 := by
  unfold toR
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, hd⟩ | ⟨h, _⟩)
    · exact absurd (den_cast_pos hx) (not_lt.mpr hd.le)
    · exact_mod_cast h
  · intro h
    exact Or.inr ⟨by exact_mod_cast h, den_cast_pos hx⟩

theorem toR_evalP (cs : List Int) {x : PairQ} (hx : 0 < x.2) :
    toR (evalP cs x) = evalZ cs (toR x) := by
  induction cs with
  | nil => simp [evalP, toR]
  | cons c cs ih =>
    have hstep : evalP (c :: cs) x = pAdd (c, 1) (pMul x (evalP cs x)) := rfl
    have hd := evalP_den_pos cs hx
    have hone : (0 : Int) < (((c : Int), (1 : Int)) : PairQ).2 := by norm_num
    rw [hstep, toR_pAdd hone (pMul_den_pos hx hd), toR_pMul hx hd, ih,
        evalZ_cons]
    congr 1
    unfold toR
    norm_num

/-! ## The Lipschitz leaf -/

theorem lip_sound {cs : List Int} {a b : PairQ}
    (ha : 0 < a.2) (hb : 0 < b.2)
    (h : checkNoRoot cs a b .lip = true) :
    ∀ x ∈ Icc (toR a) (toR b), evalZ cs x ≠ 0 := by
  intro x hx hx0
  have hab : toR a ≤ toR b := hx.1.trans hx.2
  -- denominators of everything the check computed
  have hm := pMid_den_pos ha hb
  have hM := pMax_den_pos (pAbs_den_pos ha) (pAbs_den_pos hb)
  have hB := evalP_den_pos (absZ (derivZ cs)) hM
  have hhw := pHalf_den_pos (pSub_den_pos hb ha)
  -- transfer the checked strict inequality to ℝ
  rw [checkNoRoot, pLt_iff (pMul_den_pos hB hhw) (pAbs_den_pos (evalP_den_pos cs hm)),
      toR_pMul hB hhw, toR_pAbs (evalP_den_pos cs hm),
      toR_pHalf (pSub_den_pos hb ha), toR_pSub hb ha,
      toR_evalP _ hm, toR_evalP _ hM, toR_pMid ha hb] at h
  set rm : ℝ := (toR a + toR b) / 2 with hrm
  set rM : ℝ := toR (pMax (pAbs a) (pAbs b)) with hrM
  set Breal : ℝ := evalZ (absZ (derivZ cs)) rM with hBreal
  -- h : Breal * ((toR b - toR a) / 2) < |evalZ cs rm|
  -- every point of the interval is bounded by rM in absolute value
  have hbnd : ∀ y ∈ Icc (toR a) (toR b), |y| ≤ rM := by
    intro y hy
    have : |y| ≤ max |toR a| |toR b| := abs_le_max_abs_abs hy.1 hy.2
    rwa [hrM, toR_pMax (pAbs_den_pos ha) (pAbs_den_pos hb),
        toR_pAbs ha, toR_pAbs hb]
  -- derivative bound on the interval
  have hderiv : ∀ y ∈ Icc (toR a) (toR b), ‖deriv (evalZ cs) y‖ ≤ Breal := by
    intro y hy
    rw [(hasDerivAt_evalZ cs y).deriv, Real.norm_eq_abs]
    exact abs_evalZ_le (hbnd y hy) (derivZ cs)
  have hdiff : ∀ y ∈ Icc (toR a) (toR b), DifferentiableAt ℝ (evalZ cs) y :=
    fun y _ => (hasDerivAt_evalZ cs y).differentiableAt
  have hmmem : rm ∈ Icc (toR a) (toR b) := by
    constructor <;> [skip; skip] <;> rw [hrm] <;> linarith
  -- MVT: evalZ cs is Breal-Lipschitz on the interval
  have hlip := (convex_Icc (toR a) (toR b)).norm_image_sub_le_of_norm_deriv_le
    hdiff hderiv hmmem hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hx0, zero_sub, abs_neg] at hlip
  -- |x - rm| ≤ half-width
  have hxm : |x - rm| ≤ (toR b - toR a) / 2 := by
    rw [abs_le]
    constructor <;> rw [hrm] <;> linarith [hx.1, hx.2]
  have hB0 : 0 ≤ Breal := (norm_nonneg _).trans (hderiv rm hmmem)
  have : |evalZ cs rm| ≤ Breal * ((toR b - toR a) / 2) :=
    hlip.trans (mul_le_mul_of_nonneg_left hxm hB0)
  linarith

/-! ## Main soundness theorems -/

/-- A checked `Cert` really does certify root-freeness on `[a, b]`. -/
theorem checkNoRoot_sound {cs : List Int} {a b : PairQ} {c : Cert}
    (ha : 0 < a.2) (hb : 0 < b.2)
    (h : checkNoRoot cs a b c = true) :
    ∀ x ∈ Icc (toR a) (toR b), evalZ cs x ≠ 0 := by
  induction c generalizing a b with
  | lip => exact lip_sound ha hb h
  | split m l r ihl ihr =>
    rw [checkNoRoot, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
        Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hmden, _⟩, _⟩, hl⟩, hr⟩ := h
    have hm : 0 < m.2 := by
      have := of_decide_eq_true hmden
      exact this
    intro x hx
    rcases le_total x (toR m) with hxm | hxm
    · exact ihl ha hm hl x ⟨hx.1, hxm⟩
    · exact ihr hm hb hr x ⟨hxm, hx.2⟩

/-- Helper: an integer sign product of `-1` means strictly opposite signs. -/
theorem sign_mul_sign_eq_neg_one {s t : Int} (h : s.sign * t.sign = -1) :
    (0 < s ∧ t < 0) ∨ (s < 0 ∧ 0 < t) := by
  rcases lt_trichotomy s 0 with hs | hs | hs <;>
    rcases lt_trichotomy t 0 with ht | ht | ht <;>
      simp [Int.sign_eq_neg_one_iff_neg.mpr, Int.sign_eq_one_iff_pos.mpr,
        hs, ht] at h ⊢

/-- A checked unique-root certificate really does isolate one root. -/
theorem checkUniqueRoot_sound {cs : List Int} {a b : PairQ} {dc : Cert}
    (h : checkUniqueRoot cs a b dc = true) :
    ∃! x, x ∈ Icc (toR a) (toR b) ∧ evalZ cs x = 0 := by
  rw [checkUniqueRoot, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
      Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hda, hdb⟩, hlt⟩, hsgn⟩, hnr⟩ := h
  have ha : 0 < a.2 := of_decide_eq_true hda
  have hb : 0 < b.2 := of_decide_eq_true hdb
  have hab : toR a ≤ toR b := ((pLt_iff ha hb).mp hlt).le
  have hcont : ContinuousOn (evalZ cs) (Icc (toR a) (toR b)) :=
    (continuous_evalZ cs).continuousOn
  -- endpoint signs are strictly opposite
  have hsgn' := sign_mul_sign_eq_neg_one (by exact_mod_cast of_decide_eq_true hsgn)
  have hea : toR (evalP cs a) = evalZ cs (toR a) := toR_evalP cs ha
  have heb : toR (evalP cs b) = evalZ cs (toR b) := toR_evalP cs hb
  -- existence, from the intermediate value theorem (two orientations)
  have hex : ∃ z ∈ Icc (toR a) (toR b), evalZ cs z = 0 := by
    rcases hsgn' with ⟨hpa, hpb⟩ | ⟨hpa, hpb⟩
    · -- p(a) > 0 > p(b): decreasing orientation
      have h1 : 0 < evalZ cs (toR a) := hea ▸ (toR_num_pos_iff (evalP_den_pos cs ha)).mpr hpa
      have h2 : evalZ cs (toR b) < 0 := heb ▸ (toR_num_neg_iff (evalP_den_pos cs hb)).mpr hpb
      have h0 : (0 : ℝ) ∈ Icc (evalZ cs (toR b)) (evalZ cs (toR a)) := ⟨h2.le, h1.le⟩
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' hab hcont h0
      exact ⟨z, hz, hz0⟩
    · -- p(a) < 0 < p(b): increasing orientation
      have h1 : evalZ cs (toR a) < 0 := hea ▸ (toR_num_neg_iff (evalP_den_pos cs ha)).mpr hpa
      have h2 : 0 < evalZ cs (toR b) := heb ▸ (toR_num_pos_iff (evalP_den_pos cs hb)).mpr hpb
      have h0 : (0 : ℝ) ∈ Icc (evalZ cs (toR a)) (evalZ cs (toR b)) := ⟨h1.le, h2.le⟩
      obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc hab hcont h0
      exact ⟨z, hz, hz0⟩
  -- uniqueness: the derivative is root-free, so evalZ cs is injective
  have hnr' : ∀ y ∈ Icc (toR a) (toR b), evalZ (derivZ cs) y ≠ 0 :=
    checkNoRoot_sound ha hb hnr
  have hsigninv := LeanNonlinearArith.sign_invariant_of_no_root
    (f := evalZ (derivZ cs)) (continuous_evalZ (derivZ cs)).continuousOn hnr'
  have hamem : toR a ∈ Icc (toR a) (toR b) := ⟨le_rfl, hab⟩
  have hinj : InjOn (evalZ cs) (Icc (toR a) (toR b)) := by
    rcases (hnr' (toR a) hamem).lt_or_gt with hda' | hda'
    · -- derivative negative throughout: strictly antitone
      have hmono : StrictAntiOn (evalZ cs) (Icc (toR a) (toR b)) := by
        apply strictAntiOn_of_deriv_neg (convex_Icc _ _) hcont
        intro y hy
        rw [interior_Icc] at hy
        have hy' := Ioo_subset_Icc_self hy
        rw [(hasDerivAt_evalZ cs y).deriv]
        by_contra hpos
        have h1 := (hsigninv y hy' (toR a) hamem).mp
          (lt_of_le_of_ne (not_lt.mp hpos) (hnr' y hy').symm)
        exact absurd h1 (not_lt.mpr hda'.le)
      exact hmono.injOn
    · -- derivative positive throughout: strictly monotone
      have hmono : StrictMonoOn (evalZ cs) (Icc (toR a) (toR b)) := by
        apply strictMonoOn_of_deriv_pos (convex_Icc _ _) hcont
        intro y hy
        rw [interior_Icc] at hy
        have hy' := Ioo_subset_Icc_self hy
        rw [(hasDerivAt_evalZ cs y).deriv]
        exact (hsigninv (toR a) hamem y hy').mp hda'
      exact hmono.injOn
  obtain ⟨z, hz, hz0⟩ := hex
  exact ⟨z, ⟨hz, hz0⟩, fun y ⟨hy, hy0⟩ => hinj hy hz (by rw [hy0, hz0])⟩

/-- A checked positivity certificate: `0 < evalZ cs` on all of `[a, b]`. -/
theorem checkPosOn_sound {cs : List Int} {a b : PairQ} {c : Cert}
    (h : checkPosOn cs a b c = true) :
    ∀ x ∈ Icc (toR a) (toR b), 0 < evalZ cs x := by
  rw [checkPosOn, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hda, hdb⟩, hpos⟩, hnr⟩ := h
  have ha : 0 < a.2 := of_decide_eq_true hda
  have hb : 0 < b.2 := of_decide_eq_true hdb
  intro x hx
  have hab : toR a ≤ toR b := hx.1.trans hx.2
  have hnr' := checkNoRoot_sound ha hb hnr
  have hpa : 0 < evalZ cs (toR a) :=
    toR_evalP cs ha ▸ (toR_num_pos_iff (evalP_den_pos cs ha)).mpr
      (by exact_mod_cast of_decide_eq_true hpos)
  exact (LeanNonlinearArith.sign_invariant_of_no_root
    (continuous_evalZ cs).continuousOn hnr' (toR a) ⟨le_rfl, hab⟩ x hx).mp hpa

/-- A checked negativity certificate: `evalZ cs < 0` on all of `[a, b]`. -/
theorem checkNegOn_sound {cs : List Int} {a b : PairQ} {c : Cert}
    (h : checkNegOn cs a b c = true) :
    ∀ x ∈ Icc (toR a) (toR b), evalZ cs x < 0 := by
  rw [checkNegOn, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hda, hdb⟩, hneg⟩, hnr⟩ := h
  have ha : 0 < a.2 := of_decide_eq_true hda
  have hb : 0 < b.2 := of_decide_eq_true hdb
  intro x hx
  have hab : toR a ≤ toR b := hx.1.trans hx.2
  have hnr' := checkNoRoot_sound ha hb hnr
  have hpa : evalZ cs (toR a) < 0 :=
    toR_evalP cs ha ▸ (toR_num_neg_iff (evalP_den_pos cs ha)).mpr
      (by exact_mod_cast of_decide_eq_true hneg)
  have hx0 := hnr' x hx
  have := (LeanNonlinearArith.sign_invariant_of_no_root
    (continuous_evalZ cs).continuousOn hnr' x hx (toR a) ⟨le_rfl, hab⟩).mp
  rcases lt_or_gt_of_ne hx0 with h1 | h1
  · exact h1
  · exact absurd (this h1) (not_lt.mpr hpa.le)

end LeanNonlinearArith.Certificates
