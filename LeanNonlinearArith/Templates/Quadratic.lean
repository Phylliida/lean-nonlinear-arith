import Mathlib

/-!
# Templates: Thom quadratic kit (S3; nla-19a)

The fixed lemma family behind `mk_quadratic_root`
(`nlsat_explain.cpp:886`): root atoms on a quadratic `p = a·y² + b·y + c`
are eliminated in favor of sign conditions on `disc = b² − 4ac`, `a`,
`p' ∝ 2ay + b`, and `p(y)`. Everything is a consequence of the single
ring identity

    4·a·(a·y² + b·y + c) = (2·a·y + b)² − (b² − 4·a·c)

which is why the degree-≤2 fragment needs no S1/delineability: the sign
of `p(y)` (for `a ≠ 0`) is the sign of `(2ay+b)² − disc` times the sign
of `a`, and orderings between Thom-encoded points reduce to comparing
their `(2ay+b)²` values against `disc`, with the sign of `2ay+b`
breaking the square's symmetry.

Normalization contract with the checker (`Nlsat/Check.lean`, nla-19):
atoms arrive with the *leading-coefficient sign literal* pinned by
`ensure_sign`; the checker flips `p ↦ −p` to make the leading sign
positive before instantiating this kit, so only `0 < a` ordering lemmas
are provided (the `a < 0` sign iffs are stated for completeness of the
sign dictionary). Degenerate `a = 0` falls to the pseudo-linear path
(`mk_plinear_root`) and never reaches this kit.

Everything is over a linearly ordered commutative ring — no division
anywhere (the `4a·p` trick clears it).
-/

namespace LeanNonlinearArith.Templates.Quadratic

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The one identity everything else consumes. -/
theorem quad_key (a b c y : R) :
    4 * a * (a * y ^ 2 + b * y + c) = (2 * a * y + b) ^ 2 - (b ^ 2 - 4 * a * c) := by
  ring

/-! ## Sign dictionary (`p(y)` vs `(2ay+b)²` vs `disc`) -/

theorem quad_neg_iff_pos_lead {a : R} (ha : 0 < a) (b c y : R) :
    a * y ^ 2 + b * y + c < 0 ↔ (2 * a * y + b) ^ 2 < b ^ 2 - 4 * a * c := by
  have hkey := quad_key a b c y
  have h4a : (0 : R) < 4 * a := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem quad_pos_iff_pos_lead {a : R} (ha : 0 < a) (b c y : R) :
    0 < a * y ^ 2 + b * y + c ↔ b ^ 2 - 4 * a * c < (2 * a * y + b) ^ 2 := by
  have hkey := quad_key a b c y
  have h4a : (0 : R) < 4 * a := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem quad_eq_iff {a : R} (ha : a ≠ 0) (b c y : R) :
    a * y ^ 2 + b * y + c = 0 ↔ (2 * a * y + b) ^ 2 = b ^ 2 - 4 * a * c := by
  have hkey := quad_key a b c y
  constructor
  · intro h
    rw [h, mul_zero] at hkey
    linarith
  · intro h
    rw [h] at hkey
    have h4 : (4 : R) * a ≠ 0 := by
      intro h0
      rcases mul_eq_zero.mp h0 with h4 | h4
      · exact absurd h4 (by norm_num)
      · exact ha h4
    have := sub_self (b ^ 2 - 4 * a * c)
    have hz : 4 * a * (a * y ^ 2 + b * y + c) = 0 := by rw [hkey]; ring
    exact (mul_eq_zero.mp hz).resolve_left h4

theorem quad_neg_iff_neg_lead {a : R} (ha : a < 0) (b c y : R) :
    a * y ^ 2 + b * y + c < 0 ↔ b ^ 2 - 4 * a * c < (2 * a * y + b) ^ 2 := by
  have hkey := quad_key a b c y
  have h4a : 4 * a < 0 := by nlinarith
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

theorem quad_pos_iff_neg_lead {a : R} (ha : a < 0) (b c y : R) :
    0 < a * y ^ 2 + b * y + c ↔ (2 * a * y + b) ^ 2 < b ^ 2 - 4 * a * c := by
  have hkey := quad_key a b c y
  have h4a : 4 * a < 0 := by nlinarith
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-! ## Definite cases (`disc` nonpositive: no sign change anywhere) -/

/-- `disc < 0`, positive lead: strictly positive everywhere (no roots). -/
theorem quad_pos_of_neg_disc {a : R} (ha : 0 < a) {b c : R}
    (hd : b ^ 2 - 4 * a * c < 0) (y : R) :
    0 < a * y ^ 2 + b * y + c :=
  (quad_pos_iff_pos_lead ha b c y).mpr (hd.trans_le (sq_nonneg _))

/-- `disc ≤ 0`, positive lead: nonnegative everywhere. -/
theorem quad_nonneg_of_nonpos_disc {a : R} (ha : 0 < a) {b c : R}
    (hd : b ^ 2 - 4 * a * c ≤ 0) (y : R) :
    0 ≤ a * y ^ 2 + b * y + c := by
  by_contra h
  push_neg at h
  have := (quad_neg_iff_pos_lead ha b c y).mp h
  nlinarith [sq_nonneg (2 * a * y + b)]

/-- `disc < 0`, negative lead: strictly negative everywhere. -/
theorem quad_neg_of_neg_disc {a : R} (ha : a < 0) {b c : R}
    (hd : b ^ 2 - 4 * a * c < 0) (y : R) :
    a * y ^ 2 + b * y + c < 0 :=
  (quad_neg_iff_neg_lead ha b c y).mpr (hd.trans_le (sq_nonneg _))

/-! ## Ordering family (cell bounds between Thom-encoded points)

For `0 < a` the region `{p ≤ 0}` is the (possibly empty/degenerate)
closed root interval `[r₁, r₂]`; a point with `0 < p` is strictly
outside, on the side named by the sign of `2ay + b`. These four lemmas
are the complete point-vs-root-interval order dictionary the cell
bounds need; orders between two same-side outside points or two inside
points are either linear consequences of the `2ay+b` signs or genuinely
undetermined by Thom data. -/

/-- Outside-left is left of inside(-or-boundary): `p(z) > 0`, `p'(z) < 0`,
`p(y) ≤ 0` give `z < y`. -/
theorem quad_left_of_inside {a : R} (ha : 0 < a) {b c y z : R}
    (hy : a * y ^ 2 + b * y + c ≤ 0)
    (hz : 0 < a * z ^ 2 + b * z + c)
    (hgz : 2 * a * z + b < 0) : z < y := by
  have h1 : ¬ (a * y ^ 2 + b * y + c > 0) := not_lt.mpr hy
  have hy' : (2 * a * y + b) ^ 2 ≤ b ^ 2 - 4 * a * c := by
    by_contra h
    push_neg at h
    exact h1 ((quad_pos_iff_pos_lead ha b c y).mpr h)
  have hz' : b ^ 2 - 4 * a * c < (2 * a * z + b) ^ 2 :=
    (quad_pos_iff_pos_lead ha b c z).mp hz
  by_contra hle
  push_neg at hle  -- y ≤ z
  have hgy : 2 * a * y + b ≤ 2 * a * z + b := by nlinarith
  -- then g y ≤ g z < 0 forces (g z)² ≤ (g y)², contradicting hy' < hz'
  nlinarith

/-- Outside-right is right of inside(-or-boundary): `p(z) > 0`,
`p'(z) > 0`, `p(y) ≤ 0` give `y < z`. -/
theorem quad_right_of_inside {a : R} (ha : 0 < a) {b c y z : R}
    (hy : a * y ^ 2 + b * y + c ≤ 0)
    (hz : 0 < a * z ^ 2 + b * z + c)
    (hgz : 0 < 2 * a * z + b) : y < z := by
  have h1 : ¬ (a * y ^ 2 + b * y + c > 0) := not_lt.mpr hy
  have hy' : (2 * a * y + b) ^ 2 ≤ b ^ 2 - 4 * a * c := by
    by_contra h
    push_neg at h
    exact h1 ((quad_pos_iff_pos_lead ha b c y).mpr h)
  have hz' : b ^ 2 - 4 * a * c < (2 * a * z + b) ^ 2 :=
    (quad_pos_iff_pos_lead ha b c z).mp hz
  by_contra hle
  push_neg at hle  -- z ≤ y
  have hgy : 2 * a * z + b ≤ 2 * a * y + b := by nlinarith
  nlinarith

/-- Strict outside-left vs root: `p(z) > 0`, `p'(z) < 0`, `p(y) = 0`
give `z < y` (special case of `quad_left_of_inside`, named for the
checker's ROOT_EQ path). -/
theorem quad_left_of_root {a : R} (ha : 0 < a) {b c y z : R}
    (hy : a * y ^ 2 + b * y + c = 0)
    (hz : 0 < a * z ^ 2 + b * z + c)
    (hgz : 2 * a * z + b < 0) : z < y :=
  quad_left_of_inside ha hy.le hz hgz

/-- Strict outside-right vs root. -/
theorem quad_right_of_root {a : R} (ha : 0 < a) {b c y z : R}
    (hy : a * y ^ 2 + b * y + c = 0)
    (hz : 0 < a * z ^ 2 + b * z + c)
    (hgz : 0 < 2 * a * z + b) : y < z :=
  quad_right_of_inside ha hy.le hz hgz

/-- The two roots order by their `p'` signs: `p(y) = p(z) = 0`,
`p'(y) < 0 ≤ p'(z)` (or strict) give `y ≤ z`, strictly when `p'` signs
are strict. Linear consequence, recorded for the checker. -/
theorem quad_roots_order {a : R} (ha : 0 < a) {b y z : R}
    (hgy : 2 * a * y + b < 0)
    (hgz : 0 < 2 * a * z + b) : y < z := by
  nlinarith

/-! ## Single-root case (`disc = 0`): everything collapses to `2ay + b` -/

/-- `disc = 0`, positive lead: `p(y) = 0 ↔ 2ay + b = 0`. -/
theorem quad_zero_disc_root_iff {a : R} (ha : a ≠ 0) {b c : R}
    (hd : b ^ 2 - 4 * a * c = 0) (y : R) :
    a * y ^ 2 + b * y + c = 0 ↔ 2 * a * y + b = 0 := by
  rw [quad_eq_iff ha, hd, sq_eq_zero_iff]


/-! ## Sqrt-characterized roots and the point-vs-root dictionary (ℝ)

The S3 family extension the 19a emission grammar needs (BOARD nla-19a,
Q1): the Thom encoding's root atoms get *values* via `Real.sqrt`, and
every point-vs-root comparison is a first-order consequence of the sign
dictionary above. Stated for POSITIVE lead only — the checker's
normalization contract (flip `p ↦ −p` when `A < 0`, roots unchanged) is
discharged in `Nlsat/Check.lean`. -/

section Sqrt

open Real

variable {A B C : ℝ}

/-- The i-th root of `A·y² + B·y + C` for POSITIVE lead, sqrt form:
`r₁ = (−B − √disc)/(2A)`, `r₂ = (−B + √disc)/(2A)`. -/
noncomputable def quadRoot (i : Nat) (A B C : ℝ) : ℝ :=
  (-B + (if i = 1 then -1 else 1) * Real.sqrt (B^2 - 4*A*C)) / (2*A)

theorem twoA_mul_quadRoot_add (hA : A ≠ 0) (i : Nat) :
    2 * A * quadRoot i A B C + B =
      (if i = 1 then -1 else 1) * Real.sqrt (B^2 - 4*A*C) := by
  unfold quadRoot
  field_simp
  ring

theorem quadRoot_is_root (hA : A ≠ 0) (hd : 0 ≤ B^2 - 4*A*C) (i : Nat) :
    A * (quadRoot i A B C)^2 + B * (quadRoot i A B C) + C = 0 := by
  have h1 := twoA_mul_quadRoot_add (B := B) (C := C) hA i
  have h2 := quad_key A B C (quadRoot i A B C)
  rw [h1] at h2
  have h3 : ((if i = 1 then -1 else 1 : ℝ) * Real.sqrt (B^2 - 4*A*C))^2 =
      B^2 - 4*A*C := by
    by_cases hi : i = 1 <;> simp [hi, Real.sq_sqrt hd]
  rw [h3] at h2
  have h4A : (4 : ℝ) * A ≠ 0 := mul_ne_zero (by norm_num) hA
  have : (4 : ℝ) * A * (A * (quadRoot i A B C)^2 + B * (quadRoot i A B C) + C) = 0 := by
    linarith
  exact (mul_eq_zero.mp this).resolve_left h4A

theorem quadRoot_lt (hA : 0 < A) (hd : 0 < B^2 - 4*A*C) :
    quadRoot 1 A B C < quadRoot 2 A B C := by
  unfold quadRoot
  have hsp : 0 < Real.sqrt (B^2 - 4*A*C) := Real.sqrt_pos_of_pos hd
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  have h : (-B + -1 * Real.sqrt (B^2 - 4*A*C)) < (-B + 1 * Real.sqrt (B^2 - 4*A*C)) := by
    linarith
  exact div_lt_div_of_pos_right h h2A

theorem quadRoot_eq_of_disc_zero (hA : A ≠ 0) (hd : B^2 - 4*A*C = 0) (i : Nat) :
    quadRoot i A B C = -B / (2 * A) := by
  unfold quadRoot
  rw [hd, Real.sqrt_zero, mul_zero, add_zero]

/-- Key step: `z² > disc ⟺ |z| > √disc`. -/
theorem sq_gt_disc_iff_abs_gt_sqrt {z : ℝ} (hd : 0 ≤ B^2 - 4*A*C) :
    (B^2 - 4*A*C) < z^2 ↔ Real.sqrt (B^2 - 4*A*C) < |z| := by
  constructor
  · intro h
    have h1 : (Real.sqrt (B^2 - 4*A*C))^2 < |z|^2 := by
      rwa [Real.sq_sqrt hd, sq_abs]
    exact (sq_lt_sq₀ (Real.sqrt_nonneg _) (abs_nonneg z)).mp h1
  · intro h
    have h1 : |Real.sqrt (B^2 - 4*A*C)| < |z| := by
      rwa [abs_of_nonneg (Real.sqrt_nonneg _)]
    have h2 := (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg z)).mpr h1
    rwa [abs_of_nonneg (Real.sqrt_nonneg _), sq_abs, Real.sq_sqrt hd] at h2

/-- `z² ≥ disc ⟺ |z| ≥ √disc`. -/
theorem sq_ge_disc_iff_abs_ge_sqrt {z : ℝ} (hd : 0 ≤ B^2 - 4*A*C) :
    (B^2 - 4*A*C) ≤ z^2 ↔ Real.sqrt (B^2 - 4*A*C) ≤ |z| := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have h1 : z^2 < B^2 - 4*A*C := by
      have h2 := (sq_lt_sq₀ (abs_nonneg z) (Real.sqrt_nonneg _)).mpr hc
      rwa [sq_abs, Real.sq_sqrt hd] at h2
    linarith
  · intro h
    by_contra hc
    push_neg at hc
    have h2 := (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg z)).mpr h
    rw [Real.sq_sqrt hd, sq_abs] at h2
    linarith

/-- The strict point-vs-first-root dictionary. -/
theorem lt_quadRoot1_iff (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C) (y : ℝ) :
    y < quadRoot 1 A B C ↔ 0 < A * y^2 + B * y + C ∧ 2 * A * y + B < 0 := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  have hr : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by
    have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 1
    simpa using this
  have key1 : y < quadRoot 1 A B C ↔ 2 * A * y + B < -Real.sqrt (B^2 - 4*A*C) := by
    rw [← hr]
    constructor
    · intro h
      have := (mul_lt_mul_left h2A).mpr h
      linarith
    · intro h
      have hmul : 2 * A * y < 2 * A * quadRoot 1 A B C := by linarith
      exact (mul_lt_mul_left h2A).mp hmul
  rw [key1]
  have key2 : (2 * A * y + B < -Real.sqrt (B^2 - 4*A*C)) ↔
      (Real.sqrt (B^2 - 4*A*C) < |2 * A * y + B| ∧ 2 * A * y + B < 0) := by
    constructor
    · intro h
      have hneg : 2 * A * y + B < 0 := by
        have hnn := Real.sqrt_nonneg (B^2 - 4*A*C)
        linarith
      refine ⟨?_, hneg⟩
      rw [abs_of_neg hneg]
      linarith
    · intro ⟨h1, h2⟩
      rw [abs_of_neg h2] at h1
      linarith
  rw [key2, ← sq_gt_disc_iff_abs_gt_sqrt hd, ← quad_pos_iff_pos_lead hA B C y]

/-- The strict point-vs-second-root dictionary. -/
theorem quadRoot2_lt_iff (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C) (y : ℝ) :
    quadRoot 2 A B C < y ↔ 0 < A * y^2 + B * y + C ∧ 0 < 2 * A * y + B := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  have hr : 2 * A * quadRoot 2 A B C + B = Real.sqrt (B^2 - 4*A*C) := by
    have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 2
    simpa using this
  have key1 : quadRoot 2 A B C < y ↔ Real.sqrt (B^2 - 4*A*C) < 2 * A * y + B := by
    rw [← hr]
    constructor
    · intro h
      have := (mul_lt_mul_left h2A).mpr h
      linarith
    · intro h
      have hmul : 2 * A * quadRoot 2 A B C < 2 * A * y := by linarith
      exact (mul_lt_mul_left h2A).mp hmul
  rw [key1]
  have key2 : (Real.sqrt (B^2 - 4*A*C) < 2 * A * y + B) ↔
      (Real.sqrt (B^2 - 4*A*C) < |2 * A * y + B| ∧ 0 < 2 * A * y + B) := by
    constructor
    · intro h
      have hpos : 0 < 2 * A * y + B := by
        have hnn := Real.sqrt_nonneg (B^2 - 4*A*C)
        linarith
      refine ⟨?_, hpos⟩
      rw [abs_of_pos hpos]
      exact h
    · intro ⟨h1, h2⟩
      rwa [abs_of_pos h2] at h1
  rw [key2, ← sq_gt_disc_iff_abs_gt_sqrt hd, ← quad_pos_iff_pos_lead hA B C y]

/-- The non-strict first-root dictionary (full_dimensional GE path). -/
theorem le_quadRoot1_iff (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C) (y : ℝ) :
    y ≤ quadRoot 1 A B C ↔ 0 ≤ A * y^2 + B * y + C ∧ 2 * A * y + B ≤ 0 := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  have hr : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by
    have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 1
    simpa using this
  have key1 : y ≤ quadRoot 1 A B C ↔ 2 * A * y + B ≤ -Real.sqrt (B^2 - 4*A*C) := by
    rw [← hr]
    constructor
    · intro h
      have := (mul_le_mul_left h2A).mpr h
      linarith
    · intro h
      have hmul : 2 * A * y ≤ 2 * A * quadRoot 1 A B C := by linarith
      exact (mul_le_mul_left h2A).mp hmul
  rw [key1]
  have key2 : (2 * A * y + B ≤ -Real.sqrt (B^2 - 4*A*C)) ↔
      (Real.sqrt (B^2 - 4*A*C) ≤ |2 * A * y + B| ∧ 2 * A * y + B ≤ 0) := by
    constructor
    · intro h
      have hneg : 2 * A * y + B ≤ 0 := by
        have hnn := Real.sqrt_nonneg (B^2 - 4*A*C)
        linarith
      refine ⟨?_, hneg⟩
      rw [abs_of_nonpos hneg]
      linarith
    · intro ⟨h1, h2⟩
      rw [abs_of_nonpos h2] at h1
      linarith
  rw [key2, ← sq_ge_disc_iff_abs_ge_sqrt hd]
  have key3 : (B^2 - 4*A*C) ≤ (2 * A * y + B)^2 ↔ 0 ≤ A * y^2 + B * y + C := by
    have hkey := quad_key A B C y
    have h4A : (0 : ℝ) < 4 * A := by positivity
    constructor <;> intro h <;> nlinarith
  rw [key3]

/-- The non-strict second-root dictionary (full_dimensional LE path). -/
theorem le_quadRoot2_iff (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C) (y : ℝ) :
    quadRoot 2 A B C ≤ y ↔ 0 ≤ A * y^2 + B * y + C ∧ 0 ≤ 2 * A * y + B := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  have hr : 2 * A * quadRoot 2 A B C + B = Real.sqrt (B^2 - 4*A*C) := by
    have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 2
    simpa using this
  have key1 : quadRoot 2 A B C ≤ y ↔ Real.sqrt (B^2 - 4*A*C) ≤ 2 * A * y + B := by
    rw [← hr]
    constructor
    · intro h
      have := (mul_le_mul_left h2A).mpr h
      linarith
    · intro h
      have hmul : 2 * A * quadRoot 2 A B C ≤ 2 * A * y := by linarith
      exact (mul_le_mul_left h2A).mp hmul
  rw [key1]
  have key2 : (Real.sqrt (B^2 - 4*A*C) ≤ 2 * A * y + B) ↔
      (Real.sqrt (B^2 - 4*A*C) ≤ |2 * A * y + B| ∧ 0 ≤ 2 * A * y + B) := by
    constructor
    · intro h
      have hpos : 0 ≤ 2 * A * y + B := by
        have hnn := Real.sqrt_nonneg (B^2 - 4*A*C)
        linarith
      refine ⟨?_, hpos⟩
      rw [abs_of_nonneg hpos]
      exact h
    · intro ⟨h1, h2⟩
      rwa [abs_of_nonneg h2] at h1
  rw [key2, ← sq_ge_disc_iff_abs_ge_sqrt hd]
  have key3 : (B^2 - 4*A*C) ≤ (2 * A * y + B)^2 ↔ 0 ≤ A * y^2 + B * y + C := by
    have hkey := quad_key A B C y
    have h4A : (0 : ℝ) < 4 * A := by positivity
    constructor <;> intro h <;> nlinarith
  rw [key3]

/-- At a root, the derivative sign picks WHICH root (for `disc ≥ 0`,
positive lead): `y = r₁ ⟺ p' (y) ≤ 0`. -/
theorem eq_quadRoot1_iff (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C)
    (hp : A * y^2 + B * y + C = 0) :
    y = quadRoot 1 A B C ↔ 2 * A * y + B ≤ 0 := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  by_cases hd0 : B^2 - 4*A*C = 0
  · -- double root: everything is `-B/(2A)` and `p(y)=0 ⟺ p'=0`
    rw [quadRoot_eq_of_disc_zero (ne_of_gt hA) hd0 1]
    rw [quad_zero_disc_root_iff (ne_of_gt hA) hd0 y] at hp
    rw [hp]
    constructor
    · intro h
      have : (0 : ℝ) ≤ 2 * A := le_of_lt h2A
      field_simp at h ⊢
      nlinarith
    · intro h
      field_simp at h ⊢
      nlinarith
  · have hd' : 0 < B^2 - 4*A*C := lt_of_le_of_ne hd (fun h => hd0 h.symm)
    have hlt := quadRoot_lt hA hd'
    have hr1 : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by
      have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 1
      simpa using this
    have hr2 : 2 * A * quadRoot 2 A B C + B = Real.sqrt (B^2 - 4*A*C) := by
      have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 2
      simpa using this
    -- p(y) = 0 ⟺ z² = disc: y is one of the two roots
    have hz : (2 * A * y + B)^2 = B^2 - 4*A*C := (quad_eq_iff (ne_of_gt hA) B C y).mp hp
    have habs : |2 * A * y + B| = Real.sqrt (B^2 - 4*A*C) := by
      have h3 : (2 * A * y + B)^2 = (Real.sqrt (B^2 - 4*A*C))^2 := by
        rw [Real.sq_sqrt hd]; exact hz
      have := (sq_eq_sq_iff_abs_eq_abs _ _).mp h3
      rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
    constructor
    · intro h
      rw [h, hr1]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    · intro h
      cases eq_or_eq_neg_of_abs_eq habs with
      | inl hz2 =>
        -- z = √disc > 0, contradicting z ≤ 0
        exfalso
        have hsp : 0 < Real.sqrt (B^2 - 4*A*C) := Real.sqrt_pos_of_pos hd'
        linarith
      | inr hz1 =>
        -- z = -√disc: y = r₁
        have hmul : 2 * A * y = 2 * A * quadRoot 1 A B C := by linarith
        exact mul_left_cancel₀ (ne_of_gt h2A) hmul

/-- At a root, `y = r₂ ⟺ 0 ≤ p'(y)`. -/
theorem eq_quadRoot2_iff (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C)
    (hp : A * y^2 + B * y + C = 0) :
    y = quadRoot 2 A B C ↔ 0 ≤ 2 * A * y + B := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  by_cases hd0 : B^2 - 4*A*C = 0
  · rw [quadRoot_eq_of_disc_zero (ne_of_gt hA) hd0 2]
    rw [quad_zero_disc_root_iff (ne_of_gt hA) hd0 y] at hp
    rw [hp]
    constructor
    · intro h
      have : (0 : ℝ) ≤ 2 * A := le_of_lt h2A
      field_simp at h ⊢
      nlinarith
    · intro h
      field_simp at h ⊢
      nlinarith
  · have hd' : 0 < B^2 - 4*A*C := lt_of_le_of_ne hd (fun h => hd0 h.symm)
    have hlt := quadRoot_lt hA hd'
    have hr1 : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by
      have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 1
      simpa using this
    have hr2 : 2 * A * quadRoot 2 A B C + B = Real.sqrt (B^2 - 4*A*C) := by
      have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 2
      simpa using this
    have hz : (2 * A * y + B)^2 = B^2 - 4*A*C := (quad_eq_iff (ne_of_gt hA) B C y).mp hp
    have habs : |2 * A * y + B| = Real.sqrt (B^2 - 4*A*C) := by
      have h3 : (2 * A * y + B)^2 = (Real.sqrt (B^2 - 4*A*C))^2 := by
        rw [Real.sq_sqrt hd]; exact hz
      have := (sq_eq_sq_iff_abs_eq_abs _ _).mp h3
      rwa [abs_of_nonneg (Real.sqrt_nonneg _)] at this
    constructor
    · intro h
      rw [h, hr2]
      exact Real.sqrt_nonneg _
    · intro h
      cases eq_or_eq_neg_of_abs_eq habs with
      | inl hz2 =>
        have hmul : 2 * A * y = 2 * A * quadRoot 2 A B C := by linarith
        exact mul_left_cancel₀ (ne_of_gt h2A) hmul
      | inr hz1 =>
        exfalso
        have hsp : 0 < Real.sqrt (B^2 - 4*A*C) := Real.sqrt_pos_of_pos hd'
        linarith

/-- The between-roots region: `p(y) < 0 ⟺ r₁ < y < r₂` (positive lead,
`disc > 0`). -/
theorem between_roots (hA : 0 < A) (hd : 0 < B^2 - 4*A*C)
    (hp : A * y^2 + B * y + C < 0) :
    quadRoot 1 A B C < y ∧ y < quadRoot 2 A B C := by
  have h2A : (0 : ℝ) < 2 * A := mul_pos (by norm_num) hA
  have hr1 : 2 * A * quadRoot 1 A B C + B = -Real.sqrt (B^2 - 4*A*C) := by
    have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 1
    simpa using this
  have hr2 : 2 * A * quadRoot 2 A B C + B = Real.sqrt (B^2 - 4*A*C) := by
    have := twoA_mul_quadRoot_add (B := B) (C := C) (ne_of_gt hA) 2
    simpa using this
  have hz : (2 * A * y + B)^2 < B^2 - 4*A*C := (quad_neg_iff_pos_lead hA B C y).mp hp
  have habs : |2 * A * y + B| < Real.sqrt (B^2 - 4*A*C) := by
    have h1 : |2 * A * y + B|^2 < (Real.sqrt (B^2 - 4*A*C))^2 := by
      rwa [sq_abs, Real.sq_sqrt (le_of_lt hd)]
    exact (sq_lt_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp h1
  have h2 := abs_lt.mp habs
  constructor
  · have hmul : 2 * A * quadRoot 1 A B C < 2 * A * y := by linarith
    exact (mul_lt_mul_left h2A).mp hmul
  · have hmul : 2 * A * y < 2 * A * quadRoot 2 A B C := by linarith
    exact (mul_lt_mul_left h2A).mp hmul

/-- `p(y) > 0` with `p'(y) = 0` is impossible for `disc ≥ 0` (at the
vertex, `4A·p = −disc ≤ 0`). -/
theorem not_pos_of_pderiv_eq_zero (hA : 0 < A) (hd : 0 ≤ B^2 - 4*A*C)
    (hz : 2 * A * y + B = 0) : ¬ 0 < A * y^2 + B * y + C := by
  have hkey := quad_key A B C y
  rw [hz] at hkey
  have h4A : (0 : ℝ) < 4 * A := by positivity
  nlinarith

end Sqrt

end LeanNonlinearArith.Templates.Quadratic
