import Mathlib

/-!
# Templates: order lemmas (RULES.md rows O1–O4)

Schemas from `nla_order_lemmas.cpp`: multiplication respects order with a
sign-known multiplier, and its cancellation converses. O3 (equality congruence)
is `congrArg`-trivial at instantiation; O4 composes O2 with B1 rewriting plus
`order_transfer` below.
-/

namespace LeanNonlinearArith.Templates.Order

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-! ## O1 — binomial sign: constant pivot (4 sign variants) -/

theorem mul_le_pivot_of_pos (x y a : R) (hy : 0 < y) (hx : x ≤ a) :
    x * y ≤ a * y :=
  mul_le_mul_of_nonneg_right hx hy.le

theorem mul_ge_pivot_of_pos (x y a : R) (hy : 0 < y) (hx : a ≤ x) :
    a * y ≤ x * y :=
  mul_le_mul_of_nonneg_right hx hy.le

theorem mul_le_pivot_of_neg (x y a : R) (hy : y < 0) (hx : a ≤ x) :
    x * y ≤ a * y :=
  mul_le_mul_of_nonpos_right hx hy.le

theorem mul_ge_pivot_of_neg (x y a : R) (hy : y < 0) (hx : x ≤ a) :
    a * y ≤ x * y :=
  mul_le_mul_of_nonpos_right hx hy.le

/-! ## O2 — cancellation: `c > 0 ∧ ac ≤ bc → a ≤ b` (4 variants) -/

theorem le_of_mul_le_mul_pos (a b c : R) (hc : 0 < c) (h : a * c ≤ b * c) :
    a ≤ b :=
  le_of_mul_le_mul_right h hc

theorem lt_of_mul_lt_mul_pos (a b c : R) (hc : 0 < c) (h : a * c < b * c) :
    a < b := by
  nlinarith

theorem le_of_mul_le_mul_neg (a b c : R) (hc : c < 0) (h : a * c ≤ b * c) :
    b ≤ a := by
  nlinarith

theorem lt_of_mul_lt_mul_neg (a b c : R) (hc : c < 0) (h : a * c < b * c) :
    b < a := by
  nlinarith

/-! ## O4 — order transfer between monomials sharing an equivalent factor:
`ac` vs `bd` with `|c| = |d|` reduces to a common positive magnitude `e`. -/

theorem order_transfer (A B e : R) (he : 0 < e) (h : A < B) : A * e < B * e :=
  mul_lt_mul_of_pos_right h he

theorem order_transfer_le (A B e : R) (he : 0 < e) (h : A ≤ B) : A * e ≤ B * e :=
  mul_le_mul_of_nonneg_right h he.le

end LeanNonlinearArith.Templates.Order
