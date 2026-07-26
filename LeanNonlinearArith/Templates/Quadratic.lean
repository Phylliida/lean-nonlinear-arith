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

end LeanNonlinearArith.Templates.Quadratic
