import Mathlib
import LeanNonlinearArith.Templates.Intervals
import LeanNonlinearArith.Templates.Divisions
import LeanNonlinearArith.Templates.Tangent

/-!
# nla-05 slice 1: the saturation tactic, smallest end-to-end version

Pipeline (deterministic, model-free — see BOARD.md nla-05 design sketch):
1. **collect** — walk hypotheses + goal for `ℤ` products with two non-literal
   sides; postorder, so nested monomials are processed inner-first;
2. **generate** — for each monomial `a * b`, instantiate the sign/zero rule
   vocabulary below; premises are discharged by `assumption <|> omega`
   (assumption picks up facts noted for inner monomials, omega closes linear
   consequences of the hypotheses) through a sandboxed, memoized discharge
   oracle with a per-factor sign lattice and a meta-level fast path for
   literal-vs-literal side conditions (DESIGN-discharge-oracle.md §1 + §3
   v0.5);
3. **abstract** — revert propositional hypotheses, `generalize` each monomial
   (inner-first) to a fresh variable, reintroduce: the context is now linear;
4. **leaf** — `omega`.

v0 scope: `ℤ` only, products only (`^` handled in a later slice), sign/zero
rules only (order/monotonicity/tangent generation follow the same skeleton).
-/

namespace LeanNonlinearArith.Tactic

open Lean Meta Elab Tactic

/-! ## Rule vocabulary (fixed names, fixed premise order) -/

section Rules
variable {a b : ℤ}

theorem sr_nonneg_nonneg (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := mul_nonneg ha hb
theorem sr_pos_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b := mul_pos ha hb
theorem sr_nonpos_nonpos (ha : a ≤ 0) (hb : b ≤ 0) : 0 ≤ a * b := by nlinarith
theorem sr_neg_neg (ha : a < 0) (hb : b < 0) : 0 < a * b := mul_pos_of_neg_of_neg ha hb
theorem sr_nonneg_nonpos (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by nlinarith
theorem sr_nonpos_nonneg (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by nlinarith
theorem sr_pos_neg (ha : 0 < a) (hb : b < 0) : a * b < 0 := by nlinarith
theorem sr_neg_pos (ha : a < 0) (hb : 0 < b) : a * b < 0 := by nlinarith
theorem sr_zero_left (b : ℤ) (ha : a = 0) : a * b = 0 := by rw [ha, zero_mul]
theorem sr_zero_right (a : ℤ) (hb : b = 0) : a * b = 0 := by rw [hb, mul_zero]
theorem sr_sq (a : ℤ) : 0 ≤ a * a := mul_self_nonneg a

/- Order rules with mined constants (RULES rows O1/M1-style bound
propagation). Premise order: a-bound, b-bound, then side conditions. -/
variable {la lb ha' hb' : ℤ}

theorem sr_lb_mul (h₁ : la ≤ a) (h₂ : lb ≤ b) (h₃ : 0 ≤ la) (h₄ : 0 ≤ lb) :
    la * lb ≤ a * b := by nlinarith

theorem sr_ub_mul (h₁ : a ≤ ha') (h₂ : b ≤ hb') (h₃ : 0 ≤ a) (h₄ : 0 ≤ b) :
    a * b ≤ ha' * hb' := by nlinarith

theorem sr_ub_neg_mul (h₁ : a ≤ ha') (h₂ : b ≤ hb') (h₃ : ha' ≤ 0) (h₄ : hb' ≤ 0) :
    ha' * hb' ≤ a * b := by nlinarith

/- Tangent-plane rules at mined constant points (RULES row T2; Z3 anchors at
model points, we anchor at hypothesis constants). Conclusions are linear in
`a`, `b` once `a*b` is abstracted. `c`/`d` are the anchor constants. -/
variable {c d : ℤ}

theorem sr_tan_ll (h₁ : c ≤ a) (h₂ : d ≤ b) : c * b + d * a - c * d ≤ a * b := by
  have := LeanNonlinearArith.Templates.Tangent.plane_ge a b c d
    (mul_nonneg (by linarith) (by linarith))
  linarith
theorem sr_tan_hh (h₁ : a ≤ c) (h₂ : b ≤ d) : c * b + d * a - c * d ≤ a * b := by
  have := LeanNonlinearArith.Templates.Tangent.plane_ge a b c d
    (sr_nonpos_nonpos (by linarith) (by linarith))
  linarith
theorem sr_tan_lh (h₁ : c ≤ a) (h₂ : b ≤ d) : a * b ≤ c * b + d * a - c * d := by
  have := LeanNonlinearArith.Templates.Tangent.plane_le a b c d
    (sr_nonneg_nonpos (by linarith) (by linarith))
  linarith
theorem sr_tan_hl (h₁ : a ≤ c) (h₂ : d ≤ b) : a * b ≤ c * b + d * a - c * d := by
  have := LeanNonlinearArith.Templates.Tangent.plane_le a b c d
    (sr_nonpos_nonneg (by linarith) (by linarith))
  linarith

/- Power rules (ring_nf normalizes repeated factors to `^`). Parity/nonzero
side conditions on the literal exponent are discharged by `decide` at
generation time. -/
variable {k : ℕ}

theorem sr_pow_even_nonneg (hk : Even k) (a : ℤ) : 0 ≤ a ^ k :=
  LeanNonlinearArith.Templates.MonomialBounds.even_pow_nonneg a k hk
theorem sr_pow_pos (k : ℕ) (ha : 0 < a) : 0 < a ^ k := pow_pos ha k
theorem sr_pow_nonneg (k : ℕ) (ha : 0 ≤ a) : 0 ≤ a ^ k := pow_nonneg ha k
theorem sr_pow_odd_neg (hk : Odd k) (ha : a < 0) : a ^ k < 0 := hk.pow_neg ha
theorem sr_pow_odd_nonpos (hk : Odd k) (ha : a ≤ 0) : a ^ k ≤ 0 := hk.pow_nonpos ha
theorem sr_pow_zero (hk : k ≠ 0) (ha : a = 0) : a ^ k = 0 := by
  rw [ha]; exact zero_pow hk

/- Const-substitution (RULES rows B9/PL1/T1/MB6): a factor mined to a point
collapses the product to an omega-linear term. -/
theorem sr_subst_left (b : ℤ) (ha : a = la) : a * b = la * b := by rw [ha]
theorem sr_subst_right (a : ℤ) (hb : b = lb) : a * b = a * lb := by rw [hb]

/- Zero-product split (RULES row B5): genuinely disjunctive conclusion; the
omega leaf case-splits on noted `∨` hypotheses. -/
theorem sr_zero_split (h : a * b = 0) : a = 0 ∨ b = 0 := mul_eq_zero.mp h

/- Square envelopes (RULES squares row): secant chord above the parabola on
a mined interval, tangent line below at a mined anchor. `s`/`p`/`t`/`q` are
pre-evaluated literals (parity: Z3 bakes evaluated constants; unevaluated
ground terms in noted facts are a leaf hazard — see the corner-fold rule). -/
theorem sr_sq_secant {lo hi s p : ℤ} (h₁ : lo ≤ a) (h₂ : a ≤ hi)
    (hs : s = lo + hi) (hp : p = lo * hi) : a ^ 2 ≤ s * a - p := by
  subst hs; subst hp
  nlinarith [mul_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr h₂)]

theorem sr_sq_tangent (a : ℤ) {t q : ℤ} (ht : t = 2 * c) (hq : q = c * c) :
    t * a - q ≤ a ^ 2 := by
  subst ht; subst hq
  nlinarith [sq_nonneg (a - c)]

/- Class C — cancellation (RULES O2/O3): comparison of a monomial pair
sharing a factor of lattice-known sign transfers to the cofactors. The
`e₁`/`e₂` premises absorb the shared factor's position within each monomial
(`Eq.refl` or `mul_comm` at instantiation). -/
section Cancel
variable {p q u v w : ℤ}

theorem sr_cancel_le_pos (e₁ : p = u * w) (e₂ : q = v * w)
    (hw : 0 < w) (h : p ≤ q) : u ≤ v := by
  subst e₁; subst e₂; exact le_of_mul_le_mul_right h hw

theorem sr_cancel_lt_pos (e₁ : p = u * w) (e₂ : q = v * w)
    (hw : 0 < w) (h : p < q) : u < v := by
  subst e₁; subst e₂; exact lt_of_mul_lt_mul_right h hw.le

theorem sr_cancel_le_neg (e₁ : p = u * w) (e₂ : q = v * w)
    (hw : w < 0) (h : p ≤ q) : v ≤ u := by
  subst e₁; subst e₂
  by_contra huv
  push_neg at huv
  have := mul_lt_mul_of_neg_right huv hw
  linarith

theorem sr_cancel_lt_neg (e₁ : p = u * w) (e₂ : q = v * w)
    (hw : w < 0) (h : p < q) : v < u := by
  subst e₁; subst e₂
  by_contra huv
  push_neg at huv
  have := mul_le_mul_of_nonpos_right huv hw.le
  linarith

theorem sr_cancel_eq (e₁ : p = u * w) (e₂ : q = v * w)
    (hw : w ≠ 0) (h : p = q) : u = v := by
  subst e₁; subst e₂; exact mul_right_cancel₀ hw h

end Cancel

/- Class C — down-propagation (Z3 `monomial_bounds::propagate_down` :318):
bounds on the product atom ÷ sign-definite divisor bounds → cofactor bound.
`β` and the side conditions are pre-evaluated literals — exact interval
division with floor/ceil rounding happens in meta code, mirroring Z3's
`dep_intervals`; the lemmas only certify the chosen `β`. `d` = divisor,
`f` = cofactor, `mv` = the product atom. -/
section DownProp
variable {mv d f ld hd lm hm β : ℤ}

theorem sr_down_ub_pos (e : mv = d * f)
    (h₀ : 0 < ld) (h₁ : ld ≤ d) (h₂ : d ≤ hd) (h₃ : mv ≤ hm)
    (c₁ : hm < ld * (β + 1)) (c₂ : hm < hd * (β + 1)) : f ≤ β := by
  subst e
  by_contra hb
  push_neg at hb
  have hb' : β + 1 ≤ f := by omega
  rcases le_or_gt 0 (β + 1) with hs | hs
  · have k₁ : d * (β + 1) ≤ d * f := mul_le_mul_of_nonneg_left hb' (by linarith)
    have k₂ : ld * (β + 1) ≤ d * (β + 1) := mul_le_mul_of_nonneg_right h₁ hs
    nlinarith
  · have k₁ : d * (β + 1) ≤ d * f := mul_le_mul_of_nonneg_left hb' (by linarith)
    have k₂ : hd * (β + 1) ≤ d * (β + 1) := mul_le_mul_of_nonpos_right h₂ hs.le
    nlinarith

theorem sr_down_lb_pos (e : mv = d * f)
    (h₀ : 0 < ld) (h₁ : ld ≤ d) (h₂ : d ≤ hd) (h₃ : lm ≤ mv)
    (c₁ : ld * (β - 1) < lm) (c₂ : hd * (β - 1) < lm) : β ≤ f := by
  subst e
  by_contra hb
  push_neg at hb
  have hb' : f ≤ β - 1 := by omega
  rcases le_or_gt 0 (β - 1) with hs | hs
  · have k₁ : d * f ≤ d * (β - 1) := mul_le_mul_of_nonneg_left hb' (by linarith)
    have k₂ : d * (β - 1) ≤ hd * (β - 1) := mul_le_mul_of_nonneg_right h₂ hs
    nlinarith
  · have k₁ : d * f ≤ d * (β - 1) := mul_le_mul_of_nonneg_left hb' (by linarith)
    have k₂ : d * (β - 1) ≤ ld * (β - 1) := mul_le_mul_of_nonpos_right h₁ hs.le
    nlinarith

/-- Single-sided variant: divisor bounded below only; sound for `0 ≤ β`. -/
theorem sr_down_ub_pos1 (e : mv = d * f)
    (h₀ : 0 < ld) (h₁ : ld ≤ d) (h₃ : mv ≤ hm)
    (c₀ : 0 ≤ β) (c₁ : hm < ld * (β + 1)) : f ≤ β := by
  subst e
  by_contra hb
  push_neg at hb
  have hb' : β + 1 ≤ f := by omega
  have k₁ : d * (β + 1) ≤ d * f := mul_le_mul_of_nonneg_left hb' (by linarith)
  have k₂ : ld * (β + 1) ≤ d * (β + 1) := mul_le_mul_of_nonneg_right h₁ (by omega)
  nlinarith

/-- Single-sided variant: divisor bounded below only; sound for `β ≤ 0`. -/
theorem sr_down_lb_pos1 (e : mv = d * f)
    (h₀ : 0 < ld) (h₁ : ld ≤ d) (h₃ : lm ≤ mv)
    (c₀ : β ≤ 0) (c₁ : ld * (β - 1) < lm) : β ≤ f := by
  subst e
  by_contra hb
  push_neg at hb
  have hb' : f ≤ β - 1 := by omega
  have k₁ : d * f ≤ d * (β - 1) := mul_le_mul_of_nonneg_left hb' (by linarith)
  have k₂ : d * (β - 1) ≤ ld * (β - 1) := mul_le_mul_of_nonpos_right h₁ (by omega)
  nlinarith

theorem sr_down_ub_neg (e : mv = d * f)
    (h₀ : hd < 0) (h₁ : ld ≤ d) (h₂ : d ≤ hd) (h₃ : lm ≤ mv)
    (c₁ : ld * (β + 1) < lm) (c₂ : hd * (β + 1) < lm) : f ≤ β := by
  subst e
  by_contra hb
  push_neg at hb
  have hb' : β + 1 ≤ f := by omega
  have k₁ : d * f ≤ d * (β + 1) := mul_le_mul_of_nonpos_left hb' (by linarith)
  rcases le_or_gt 0 (β + 1) with hs | hs
  · have k₂ : d * (β + 1) ≤ hd * (β + 1) := mul_le_mul_of_nonneg_right h₂ hs
    nlinarith
  · have k₂ : d * (β + 1) ≤ ld * (β + 1) := mul_le_mul_of_nonpos_right h₁ hs.le
    nlinarith

theorem sr_down_lb_neg (e : mv = d * f)
    (h₀ : hd < 0) (h₁ : ld ≤ d) (h₂ : d ≤ hd) (h₃ : mv ≤ hm)
    (c₁ : hm < ld * (β - 1)) (c₂ : hm < hd * (β - 1)) : β ≤ f := by
  subst e
  by_contra hb
  push_neg at hb
  have hb' : f ≤ β - 1 := by omega
  have k₁ : d * (β - 1) ≤ d * f := mul_le_mul_of_nonpos_left hb' (by linarith)
  rcases le_or_gt 0 (β - 1) with hs | hs
  · have k₂ : ld * (β - 1) ≤ d * (β - 1) := mul_le_mul_of_nonneg_right h₁ hs
    nlinarith
  · have k₂ : hd * (β - 1) ≤ d * (β - 1) := mul_le_mul_of_nonpos_right h₂ hs.le
    nlinarith

end DownProp

/- Class C — down-sign (the divisor-sign quotient of the atom's sign; omega
cannot derive these, they are nonlinear). Strict divisor, strict or weak
atom sign. -/
section DownSign
variable {mv d f : ℤ}

theorem sr_dsign_pp (e : mv = d * f) (hd : 0 < d) (hm : 0 < mv) : 0 < f := by
  subst e; by_contra h; push_neg at h
  have := mul_nonpos_of_nonneg_of_nonpos hd.le h; linarith

theorem sr_dsign_pn (e : mv = d * f) (hd : 0 < d) (hm : mv < 0) : f < 0 := by
  subst e; by_contra h; push_neg at h
  have := mul_nonneg hd.le h; linarith

theorem sr_dsign_np (e : mv = d * f) (hd : d < 0) (hm : 0 < mv) : f < 0 := by
  subst e; by_contra h; push_neg at h
  have := mul_nonpos_of_nonpos_of_nonneg hd.le h; linarith

theorem sr_dsign_nn (e : mv = d * f) (hd : d < 0) (hm : mv < 0) : 0 < f := by
  subst e; by_contra h; push_neg at h
  nlinarith [mul_nonneg (show (0:ℤ) ≤ -d by linarith) (show (0:ℤ) ≤ -f by linarith)]

theorem sr_dsign_pp' (e : mv = d * f) (hd : 0 < d) (hm : 0 ≤ mv) : 0 ≤ f := by
  subst e; by_contra h; push_neg at h
  have := mul_neg_of_pos_of_neg hd h; linarith

theorem sr_dsign_pn' (e : mv = d * f) (hd : 0 < d) (hm : mv ≤ 0) : f ≤ 0 := by
  subst e; by_contra h; push_neg at h
  have := mul_pos hd h; linarith

theorem sr_dsign_np' (e : mv = d * f) (hd : d < 0) (hm : 0 ≤ mv) : f ≤ 0 := by
  subst e; by_contra h; push_neg at h
  have := mul_neg_of_neg_of_pos hd h; linarith

theorem sr_dsign_nn' (e : mv = d * f) (hd : d < 0) (hm : mv ≤ 0) : 0 ≤ f := by
  subst e; by_contra h; push_neg at h
  have := mul_pos_of_neg_of_neg hd h; linarith

end DownSign

/- Class C — MB4/MB5 square roots: bounds on the `a^2` atom propagate to the
base. `r` is the pre-evaluated integer root (floor √ for upper bounds, ceil
√ for the lower bound); MB5's conclusion is genuinely disjunctive, matching
Z3's clause — the omega leaf case-splits on it. -/
section SqRoot
variable {u l r : ℤ}

theorem sr_sq_root_ub_hi (h : a ^ 2 ≤ u) (hr : 0 ≤ r)
    (c : u < (r + 1) * (r + 1)) : a ≤ r := by
  by_contra hb; push_neg at hb
  have hb' : r + 1 ≤ a := by omega
  nlinarith [mul_le_mul hb' hb' (by omega) (by omega)]

theorem sr_sq_root_ub_lo (h : a ^ 2 ≤ u) (hr : 0 ≤ r)
    (c : u < (r + 1) * (r + 1)) : -r ≤ a := by
  by_contra hb; push_neg at hb
  have hb' : r + 1 ≤ -a := by omega
  nlinarith [mul_le_mul hb' hb' (by omega) (by omega)]

theorem sr_sq_root_lb (h : l ≤ a ^ 2)
    (c : (r - 1) * (r - 1) < l) : a ≤ -r ∨ r ≤ a := by
  by_contra hb
  push_neg at hb
  obtain ⟨h₁, h₂⟩ := hb
  have k : a ^ 2 ≤ (r - 1) ^ 2 := sq_le_sq' (by omega) (by omega)
  nlinarith

end SqRoot

/- Class D — conditional sign/zero clauses (RULES B2-conditional/B5/B6):
unconditional ℤ tautologies, noted only in the failure-gated clause phase.
The omega leaf case-splits on each disjunction and prunes lattice-refuted
disjuncts against the context — the model-free counterpart of Z3's lazily
emitted sign clauses. -/
section Clauses

theorem sr_cl_pp (a b : ℤ) : a ≤ 0 ∨ b ≤ 0 ∨ 0 < a * b := by
  rcases le_or_gt a 0 with h | h
  · exact Or.inl h
  rcases le_or_gt b 0 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_pos h h'))

theorem sr_cl_nn (a b : ℤ) : 0 ≤ a ∨ 0 ≤ b ∨ 0 < a * b := by
  rcases le_or_gt 0 a with h | h
  · exact Or.inl h
  rcases le_or_gt 0 b with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_pos_of_neg_of_neg h h'))

theorem sr_cl_pn (a b : ℤ) : a ≤ 0 ∨ 0 ≤ b ∨ a * b < 0 := by
  rcases le_or_gt a 0 with h | h
  · exact Or.inl h
  rcases le_or_gt 0 b with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_neg_of_pos_of_neg h h'))

theorem sr_cl_np (a b : ℤ) : 0 ≤ a ∨ b ≤ 0 ∨ a * b < 0 := by
  rcases le_or_gt 0 a with h | h
  · exact Or.inl h
  rcases le_or_gt b 0 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_neg_of_neg_of_pos h h'))

theorem sr_cl_zl (a b : ℤ) : a ≠ 0 ∨ a * b = 0 := by
  rcases eq_or_ne a 0 with h | h
  · exact Or.inr (by rw [h, zero_mul])
  · exact Or.inl h

theorem sr_cl_zr (a b : ℤ) : b ≠ 0 ∨ a * b = 0 := by
  rcases eq_or_ne b 0 with h | h
  · exact Or.inr (by rw [h, mul_zero])
  · exact Or.inl h

theorem sr_cl_b5 (a b : ℤ) : a * b ≠ 0 ∨ a = 0 ∨ b = 0 := by
  rcases eq_or_ne (a * b) 0 with h | h
  · exact Or.inr (mul_eq_zero.mp h)
  · exact Or.inl h

end Clauses

/- Class D — O1 conditional order clauses: a mined pivot on one factor, the
other factor's sign left to the leaf's case split. Conclusions are linear
once the product is atomized (`p` is a literal at instantiation). -/
section O1Clauses
variable {x y p : ℤ}

theorem sr_cl_o1_ub (y : ℤ) (h : x ≤ p) : y ≤ 0 ∨ x * y ≤ p * y := by
  rcases le_or_gt y 0 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonneg_right h h'.le)

theorem sr_cl_o1_ub' (y : ℤ) (h : x ≤ p) : 0 ≤ y ∨ p * y ≤ x * y := by
  rcases le_or_gt 0 y with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonpos_right h h'.le)

theorem sr_cl_o1_lb (y : ℤ) (h : p ≤ x) : y ≤ 0 ∨ p * y ≤ x * y := by
  rcases le_or_gt y 0 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonneg_right h h'.le)

theorem sr_cl_o1_lb' (y : ℤ) (h : p ≤ x) : 0 ≤ y ∨ x * y ≤ p * y := by
  rcases le_or_gt 0 y with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonpos_right h h'.le)

theorem sr_cl_o1_ubr (x : ℤ) (h : y ≤ p) : x ≤ 0 ∨ x * y ≤ x * p := by
  rcases le_or_gt x 0 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonneg_left h h'.le)

theorem sr_cl_o1_ubr' (x : ℤ) (h : y ≤ p) : 0 ≤ x ∨ x * p ≤ x * y := by
  rcases le_or_gt 0 x with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonpos_left h h'.le)

theorem sr_cl_o1_lbr (x : ℤ) (h : p ≤ y) : x ≤ 0 ∨ x * p ≤ x * y := by
  rcases le_or_gt x 0 with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonneg_left h h'.le)

theorem sr_cl_o1_lbr' (x : ℤ) (h : p ≤ y) : 0 ≤ x ∨ x * y ≤ x * p := by
  rcases le_or_gt 0 x with h' | h'
  · exact Or.inl h'
  · exact Or.inr (mul_le_mul_of_nonpos_left h h'.le)

end O1Clauses

/- Class D — B7/B8 absolute-value rows, in `natAbs` form (omega handles
`Int.natAbs` natively, Frontend :291). natAbs facts case-split at the leaf,
so these are clause-phase only. -/
section AbsRows

theorem sr_b8_left (b : ℤ) (h : a ≠ 0) : b.natAbs ≤ (a * b).natAbs := by
  rw [Int.natAbs_mul]
  exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr h)

theorem sr_b8_right (a : ℤ) (h : b ≠ 0) : a.natAbs ≤ (a * b).natAbs := by
  rw [Int.natAbs_mul, Nat.mul_comm]
  exact Nat.le_mul_of_pos_left _ (Int.natAbs_pos.mpr h)

theorem sr_cl_b7 (a b : ℤ) :
    (a * b).natAbs ≠ a.natAbs ∨ a = 0 ∨ b = 1 ∨ b = -1 := by
  rcases eq_or_ne ((a * b).natAbs) a.natAbs with h | h
  · rcases eq_or_ne a 0 with ha | ha
    · exact Or.inr (Or.inl ha)
    · rw [Int.natAbs_mul] at h
      have ha' : 0 < a.natAbs := Int.natAbs_pos.mpr ha
      have hb : b.natAbs = 1 := Nat.eq_of_mul_eq_mul_left ha' (by omega)
      omega
  · exact Or.inl h

theorem sr_cl_b7r (a b : ℤ) :
    (a * b).natAbs ≠ b.natAbs ∨ b = 0 ∨ a = 1 ∨ a = -1 := by
  rcases eq_or_ne ((a * b).natAbs) b.natAbs with h | h
  · rcases eq_or_ne b 0 with hb | hb
    · exact Or.inr (Or.inl hb)
    · rw [Int.natAbs_mul, Nat.mul_comm] at h
      have hb' : 0 < b.natAbs := Int.natAbs_pos.mpr hb
      have ha : a.natAbs = 1 := Nat.eq_of_mul_eq_mul_left hb' (by omega)
      omega
  · exact Or.inl h

end AbsRows

end Rules

/-- Premise/conclusion shapes for the binary sign rules. -/
inductive Shape | nonneg | pos | nonpos | neg
  deriving BEq, Repr

/-- `shapeProp s x` builds the `ℤ` proposition for shape `s` about `x`. -/
def shapeProp (s : Shape) (x : Expr) : MetaM Expr := do
  let zero := mkIntLit 0
  match s with
  | .nonneg => mkAppM ``LE.le #[zero, x]
  | .pos    => mkAppM ``LT.lt #[zero, x]
  | .nonpos => mkAppM ``LE.le #[x, zero]
  | .neg    => mkAppM ``LT.lt #[x, zero]

/-- Binary sign rules: (lemma, shape of `a`-premise, shape of `b`-premise). -/
def signRules : List (Name × Shape × Shape) :=
  [(``sr_pos_pos,        .pos,    .pos),
   (``sr_neg_neg,        .neg,    .neg),
   (``sr_pos_neg,        .pos,    .neg),
   (``sr_neg_pos,        .neg,    .pos),
   (``sr_nonneg_nonneg,  .nonneg, .nonneg),
   (``sr_nonpos_nonpos,  .nonpos, .nonpos),
   (``sr_nonneg_nonpos,  .nonneg, .nonpos),
   (``sr_nonpos_nonneg,  .nonpos, .nonneg)]

/-- Destructure an `ℤ` multiplication. -/
def isIntMul? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[ty, _, _, _, a, b]) =>
    if ty.isConstOf ``Int then some (a, b) else none
  | _ => none

/-- Destructure `base ^ k` with `base : ℤ` non-literal and `k` a `ℕ` literal
`≥ 2` (lower exponents are linear). -/
def isIntPow? (e : Expr) : Option (Expr × Nat) :=
  match e.getAppFnArgs with
  | (``HPow.hPow, #[tyB, tyE, _, _, a, n]) =>
    if tyB.isConstOf ``Int && tyE.isConstOf ``Nat then
      match n.nat? with
      | some k => if k ≥ 2 && !(e.int?).isSome then some (a, k) else none
      | none => none
    else none
  | _ => none

/-- Integer literal test (numerals and their negations). -/
def isIntLit (e : Expr) : Bool :=
  (e.int?).isSome

/-- Collect monomials (ℤ products with two non-literal sides) in postorder:
inner products before the products containing them. -/
partial def collectMonomials (e : Expr) : StateRefT (Array Expr) MetaM Unit := do
  match e with
  | .app .. => do
    for arg in e.getAppArgs do
      collectMonomials arg
    -- terms under binders have loose bvars: not generalizable, skip
    if !e.hasLooseBVars then
      if let some (a, b) := isIntMul? e then
        if !isIntLit a && !isIntLit b then
          let acc ← get
          if !acc.contains e then
            modify (·.push e)
      if let some (a, _) := isIntPow? e then
        if !isIntLit a then
          let acc ← get
          if !acc.contains e then
            modify (·.push e)
  | .mdata _ b => collectMonomials b
  | .forallE _ d b _ => collectMonomials d; collectMonomials b
  | .lam _ d b _ => collectMonomials d; collectMonomials b
  | .letE _ t v b _ => collectMonomials t; collectMonomials v; collectMonomials b
  | _ => pure ()

/-- Mine literal bounds for `factor` from the propositional hypotheses:
returns (lower-bound literals, upper-bound literals). Strict bounds count —
premise discharge (omega) absorbs the strictness. Call inside the goal ctx. -/
def mineBounds (factor : Expr) : MetaM (Array Int × Array Int) := do
  let factor := factor.consumeMData
  let mut los : Array Int := #[]
  let mut his : Array Int := #[]
  -- each hypothesis yields ≤-facts (l ⋈ r): plain comparisons (GE/GT
  -- swapped), `Eq` both ways (fixed vars — Z3 propagate_fixed_var), and
  -- `¬`-wrapped comparisons (control-flow negations; Z3's LRA state holds
  -- these as bounds, so the miner must see them too)
  let cmpFacts (t : Expr) : Array (Expr × Expr × Bool) :=
    match t.getAppFnArgs with
    | (``LE.le, #[_, _, l, r]) => #[(l, r, false)]
    | (``LT.lt, #[_, _, l, r]) => #[(l, r, true)]
    | (``GE.ge, #[_, _, l, r]) => #[(r, l, false)]
    | (``GT.gt, #[_, _, l, r]) => #[(r, l, true)]
    | (``Eq, #[t', l, r]) =>
      if t'.isConstOf ``Int then #[(l, r, false), (r, l, false)] else #[]
    | (``Not, #[p]) =>
      match p.getAppFnArgs with
      | (``LT.lt, #[_, _, l, r]) => #[(r, l, false)]
      | (``LE.le, #[_, _, l, r]) => #[(r, l, true)]
      | (``GT.gt, #[_, _, l, r]) => #[(l, r, false)]
      | (``GE.ge, #[_, _, l, r]) => #[(l, r, true)]
      | _ => #[]
    | _ => #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    for (l, r, strict) in cmpFacts ty do
      -- lit ⋈ factor: lower bound (strict ℤ bound tightens by one)
      if let some v := l.int? then
        if r.consumeMData == factor then
          let v := if strict then v + 1 else v
          if !los.contains v then los := los.push v
      -- factor ⋈ lit: upper bound
      if let some v := r.int? then
        if l.consumeMData == factor then
          let v := if strict then v - 1 else v
          if !his.contains v then his := his.push v
  return (los, his)

/-- Evaluate an `ℤ` comparison whose both sides are integer literals, in meta
code. Returns `none` when the proposition is not of that shape. -/
def evalIntLitCmp? (ty : Expr) : Option Bool :=
  match ty.getAppFnArgs with
  | (``LE.le, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← l.int?) ≤ (← r.int?))
  | (``LT.lt, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← l.int?) < (← r.int?))
  | (``GE.ge, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← r.int?) ≤ (← l.int?))
  | (``GT.gt, #[t, _, l, r]) => do
    guard (t.isConstOf ``Int); return decide ((← r.int?) < (← l.int?))
  | (``Eq, #[t, l, r]) => do
    guard (t.isConstOf ``Int); return (← l.int?) == (← r.int?)
  | _ => none

/-- Discharge cache: premise type ↦ proof term (`none` = attempt failed).
Positive entries stay valid as the goal context grows — proof terms reference
fvars, and noting only adds hypotheses. Negative entries can go stale (a newly
noted fact may unblock them), so `generate` drops them after each noting
round. -/
abbrev DCache := IO.Ref (Std.HashMap Expr (Option Expr))

/-! Instrumentation counters, reported by `nla_saturate_stats`. -/
initialize nlaLitFast : IO.Ref Nat ← IO.mkRef 0
initialize nlaCacheHit : IO.Ref Nat ← IO.mkRef 0
initialize nlaTacticCall : IO.Ref Nat ← IO.mkRef 0

/-- Try to prove `ty` in the current goal's context (DESIGN-discharge-oracle
§1/§3). Three layers:
1. literal-vs-literal comparisons are decided in meta code — false ones cost
   nothing, true ones a `decide` proof, no tactic either way;
2. results are memoized in `cache` (`0 ≤ a` was previously re-proved by every
   rule that wanted it);
3. the tactic attempt (`assumption <|> omega`) is fully sandboxed: the
   instantiated proof term is extracted inside the sandbox and the elaboration
   state rolled back on both success and failure, so metavariable-context and
   info-tree growth never persist. -/
def tryDischarge (cache : DCache) (ty : Expr) : TacticM (Option Expr) := do
  if let some b := evalIntLitCmp? ty then
    nlaLitFast.modify (· + 1)
    if !b then return none
    let pf? ← try some <$> mkDecideProof ty catch _ => pure none
    if pf?.isSome then return pf?
    -- fall through to the tactic path if `decide` unexpectedly fails
  if let some r := (← cache.get).get? ty then
    nlaCacheHit.modify (· + 1)
    return r
  nlaTacticCall.modify (· + 1)
  let r ← do
    let s ← saveState
    try
      let mvar ← mkFreshExprMVar ty
      let gs ← Lean.Elab.runTactic mvar.mvarId!
        (← `(tactic| first | assumption | omega))
      if gs.1.isEmpty then
        let pf ← instantiateMVars mvar
        -- omega may have minted auxiliary env constants the proof term
        -- references; keep the environment (monotone, benign) while rolling
        -- back metavariable context and info trees. The name generator is
        -- kept forward too, so a later mint can never collide with a
        -- constant that survived in the kept environment.
        let env ← getEnv
        let ngen ← getNGen
        restoreState s
        setEnv env
        setNGen ngen
        -- the proof's syntactic type can differ from `ty` (e.g. `assumption`
        -- closes `0 < a` with `1 ≤ a` by ℤ defeq); ascribe `ty` so meta-level
        -- weakenings see the probed shape
        if pf.hasExprMVar then pure none
        else pure (some (← mkExpectedTypeHint pf ty))
      else
        restoreState s
        pure none
    catch _ =>
      restoreState s
      pure none
  cache.modify (·.insert ty r)
  return r

/-- Discharge every premise or fail. -/
def dischargeAll (cache : DCache) (tys : Array Expr) : TacticM (Option (Array Expr)) := do
  let mut pfs : Array Expr := #[]
  for ty in tys do
    match ← tryDischarge cache ty with
    | some pf => pfs := pfs.push pf
    | none => return none
  return some pfs

/-- Position of a factor in the sign lattice, with the strongest proved
fact. -/
inductive SignFacts where
  | zero (pf : Expr)     -- x = 0
  | pos (pf : Expr)      -- 0 < x
  | neg (pf : Expr)      -- x < 0
  | nonneg (pf : Expr)   -- 0 ≤ x
  | nonpos (pf : Expr)   -- x ≤ 0
  | unknown

/-- `true` when the lattice pinned any sign information. -/
def SignFacts.isKnown : SignFacts → Bool
  | .unknown => false
  | _ => true

/-- Weaken a lattice fact to the requested premise shape in meta code (zero
tactic calls): `pos → nonneg` and `neg → nonpos` by `le_of_lt`, `zero → both`
by `le_of_eq`. -/
def SignFacts.shapePf? (si : SignFacts) (s : Shape) : MetaM (Option Expr) := do
  match s, si with
  | .pos,    .pos pf    => return some pf
  | .neg,    .neg pf    => return some pf
  | .nonneg, .pos pf    => return some (← mkAppM ``le_of_lt #[pf])
  | .nonneg, .nonneg pf => return some pf
  | .nonneg, .zero pf   => return some (← mkAppM ``le_of_eq #[← mkAppM ``Eq.symm #[pf]])
  | .nonpos, .neg pf    => return some (← mkAppM ``le_of_lt #[pf])
  | .nonpos, .nonpos pf => return some pf
  | .nonpos, .zero pf   => return some (← mkAppM ``le_of_eq #[pf])
  | _, _ => return none

/-- Locate `x` in the sign lattice with ≤ 3 discharge calls (DESIGN §3 v0.5):
probe `0 ≤ x` and refine to pos/zero, else probe `x ≤ 0` and refine to neg.
All sign/zero/pow rules then instantiate from the result with no further
tactic calls. Recomputation for a repeated factor costs only cache lookups. -/
def signFactsFor (cache : DCache) (x : Expr) : TacticM SignFacts := do
  let zero := mkIntLit 0
  if let some pf := ← tryDischarge cache (← mkAppM ``LE.le #[zero, x]) then
    if let some pfp := ← tryDischarge cache (← mkAppM ``LT.lt #[zero, x]) then
      return .pos pfp
    if let some pfz := ← tryDischarge cache (← mkAppM ``Eq #[x, zero]) then
      return .zero pfz
    return .nonneg pf
  if let some pf := ← tryDischarge cache (← mkAppM ``LE.le #[x, zero]) then
    if let some pfn := ← tryDischarge cache (← mkAppM ``LT.lt #[x, zero]) then
      return .neg pfn
    return .nonpos pf
  return .unknown

/-- Noted-conclusion set for multi-round dedup: syntactic types of every
hypothesis already in the context (seeded) plus every fact noted so far.
Structural `Expr` equality suffices — re-derivations of the same rule
instantiation are built by the same `mkAppM` calls, so they collide exactly.
Distinct-but-equivalent forms slip through, which only costs a redundant
hypothesis, never soundness. -/
abbrev NotedSet := IO.Ref (Std.HashSet Expr)

/-- Note a fact into the goal context unless its conclusion is already
present (dedup for the multi-round loop). The name is freshened so generated
hypotheses can never capture or collide with user hypotheses. Returns `true`
iff the fact was new. -/
def noteFact (noted : NotedSet) (name : Name) (concl proof : Expr) :
    TacticM Bool := do
  let key := (← instantiateMVars concl).consumeMData
  if (← noted.get).contains key then
    return false
  noted.modify (·.insert key)
  let g ← getMainGoal
  let (_, g') ← g.note (← mkFreshUserName name) proof (some concl)
  replaceMainGoal [g']
  return true

/-- Facts derived for one monomial, computed inside the current goal's
context so premise discharge sees previously noted facts. -/
def factsFor (cache : DCache) (m : Expr) (idx : Nat) :
    TacticM (Array (Name × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let some (a, b) := isIntMul? m | return #[]
    let mut out : Array (Name × Expr × Expr) := #[]
    -- squares: unconditional
    if a == b then
      let pf ← mkAppM ``sr_sq #[a]
      out := out.push (.mkSimple s!"nla_sq_{idx}", ← inferType pf, pf)
    -- sign lattice per factor, once; zero/sign rules read it with no
    -- further tactic calls
    let siA ← signFactsFor cache a
    let siB ← signFactsFor cache b
    -- zero rules
    if let .zero pa := siA then
      let pf ← mkAppM ``sr_zero_left #[b, pa]
      out := out.push (.mkSimple s!"nla_zero_{idx}", ← inferType pf, pf)
    else if let .zero pb := siB then
      let pf ← mkAppM ``sr_zero_right #[a, pb]
      out := out.push (.mkSimple s!"nla_zero_{idx}", ← inferType pf, pf)
    else
      -- B5 zero-product split: m provably zero with neither factor's zero
      -- known — note the disjunction; the omega leaf splits on `∨` hyps
      if let some pm := ← tryDischarge cache (← mkAppM ``Eq #[m, mkIntLit 0]) then
        let pf ← mkAppM ``sr_zero_split #[pm]
        out := out.push (.mkSimple s!"nla_zsplit_{idx}", ← inferType pf, pf)
    -- binary sign rules: first rule both of whose premise shapes the
    -- lattice can serve wins
    for (lem, sa, sb) in signRules do
      let some pa ← siA.shapePf? sa | continue
      let some pb ← siB.shapePf? sb | continue
      let pf ← mkAppM lem #[pa, pb]
      out := out.push (.mkSimple s!"nla_sign_{idx}", ← inferType pf, pf)
      break
    -- order rules with mined constants (O1/M1-style bound propagation)
    let (losA, hisA) ← mineBounds a
    let (losB, hisB) ← mineBounds b
    let zero := mkIntLit 0
    let le (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
    -- const-substitution (RULES B9/PL1/T1/MB6): factor mined to a point →
    -- product collapses to an omega-linear term (unlike the tangent pairs,
    -- this needs nothing about the other factor)
    for c in losA do
      if hisA.contains c then
        if let some pfs := ← dischargeAll cache #[← le (mkIntLit c) a, ← le a (mkIntLit c)] then
          let pfEq ← mkAppM ``le_antisymm #[pfs[1]!, pfs[0]!]
          let pf ← mkAppM ``sr_subst_left #[b, pfEq]
          out := out.push (.mkSimple s!"nla_cst_{idx}_{out.size}", ← inferType pf, pf)
    for c in losB do
      if hisB.contains c then
        if let some pfs := ← dischargeAll cache #[← le (mkIntLit c) b, ← le b (mkIntLit c)] then
          let pfEq ← mkAppM ``le_antisymm #[pfs[1]!, pfs[0]!]
          let pf ← mkAppM ``sr_subst_right #[a, pfEq]
          out := out.push (.mkSimple s!"nla_cst_{idx}_{out.size}", ← inferType pf, pf)
    for lav in losA do
      for lbv in losB do
        let la := mkIntLit lav
        let lb := mkIntLit lbv
        let prems := #[← le la a, ← le lb b, ← le zero la, ← le zero lb]
        if let some pfs := ← dischargeAll cache prems then
          let pf ← mkAppM ``sr_lb_mul pfs
          out := out.push (.mkSimple s!"nla_lb_{idx}_{out.size}", ← inferType pf, pf)
    for hiav in hisA do
      for hibv in hisB do
        let hia := mkIntLit hiav
        let hib := mkIntLit hibv
        let premsN := #[← le a hia, ← le b hib, ← le zero a, ← le zero b]
        if let some pfs := ← dischargeAll cache premsN then
          let pf ← mkAppM ``sr_ub_mul pfs
          out := out.push (.mkSimple s!"nla_ub_{idx}_{out.size}", ← inferType pf, pf)
        let premsP := #[← le a hia, ← le b hib, ← le hia zero, ← le hib zero]
        if let some pfs := ← dischargeAll cache premsP then
          let pf ← mkAppM ``sr_ub_neg_mul pfs
          out := out.push (.mkSimple s!"nla_ubn_{idx}_{out.size}", ← inferType pf, pf)
    -- tangent planes anchored at mined constants (linear conclusions)
    let tangentCombos : List (Name × Array Int × Array Int × Bool × Bool) :=
      [(``sr_tan_ll, losA, losB, true,  true),
       (``sr_tan_hh, hisA, hisB, false, false),
       (``sr_tan_lh, losA, hisB, true,  false),
       (``sr_tan_hl, hisA, losB, false, true)]
    for (lem, csA, csB, aLower, bLower) in tangentCombos do
      for cv in csA do
        for dv in csB do
          let cE := mkIntLit cv
          let dE := mkIntLit dv
          let pA ← if aLower then le cE a else le a cE
          let pB ← if bLower then le dE b else le b dE
          if let some pfs := ← dischargeAll cache #[pA, pB] then
            let pf ← mkAppM lem pfs
            out := out.push
              (.mkSimple s!"nla_tan_{idx}_{out.size}", ← inferType pf, pf)
    -- full intervals: corner-product bounds (Templates.Intervals)
    for lav in losA do
      for hiav in hisA do
        for lbv in losB do
          for hibv in hisB do
            let la := mkIntLit lav
            let hia := mkIntLit hiav
            let lb := mkIntLit lbv
            let hib := mkIntLit hibv
            let prems := #[← le la a, ← le a hia, ← le lb b, ← le b hib]
            if let some pfs := ← dischargeAll cache prems then
              -- fold the corner min/max to a single literal HERE: noted
              -- `min`/`max` facts make the omega leaf case-split per
              -- occurrence, which is exponential in the number of corner
              -- facts (measured: 168s leaf on an 8-monomial goal)
              let corners := #[lav * lbv, lav * hibv, hiav * lbv, hiav * hibv]
              let hiV := corners.foldl max corners[0]!
              let loV := corners.foldl min corners[0]!
              let pfHi ← mkAppM ``Templates.Intervals.mul_le_max_corners pfs
              if let (``LE.le, #[_, _, _, maxE]) := (← inferType pfHi).getAppFnArgs then
                let pfStep ← mkDecideProof (← le maxE (mkIntLit hiV))
                let pf ← mkAppM ``le_trans #[pfHi, pfStep]
                out := out.push
                  (.mkSimple s!"nla_chi_{idx}_{out.size}", ← inferType pf, pf)
              let pfLo ← mkAppM ``Templates.Intervals.min_corners_le_mul pfs
              if let (``LE.le, #[_, _, minE, _]) := (← inferType pfLo).getAppFnArgs then
                let pfStep ← mkDecideProof (← le (mkIntLit loV) minE)
                let pf ← mkAppM ``le_trans #[pfStep, pfLo]
                out := out.push
                  (.mkSimple s!"nla_clo_{idx}_{out.size}", ← inferType pf, pf)
    -- class C down-propagation (Z3 monomial_bounds propagate_down :318):
    -- atom bounds ÷ sign-definite divisor bounds → cofactor bounds. β is
    -- computed by exact interval division in meta (floor/ceil); the side
    -- conditions are then checked numerically and certified by decide, so
    -- a wrong β formula can only lose tightness, never soundness.
    let (losM, hisM) ← mineBounds m
    let siM ← signFactsFor cache m
    let lt' (x y : Expr) : MetaM Expr := mkAppM ``LT.lt #[x, y]
    let mulE (x y : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[x, y]
    let bOff (v off : Int) : MetaM Expr :=
      if off ≥ 0 then mkAppM ``HAdd.hAdd #[mkIntLit v, mkIntLit off]
      else mkAppM ``HSub.hSub #[mkIntLit v, mkIntLit (-off)]
    let cdiv (x y : Int) : Int := -((-x).fdiv y)
    for (dvsr, si, cofSi, losD0, hisD0, losCof, hisCof, comm) in
        #[(a, siA, siB, losA, hisA, losB, hisB, false),
          (b, siB, siA, losB, hisB, losA, hisA, true)] do
      let mkE : MetaM Expr :=
        if comm then mkAppM ``mul_comm #[a, b] else mkEqRefl m
      -- lattice strengthening: strict sign gives the integer unit bound
      let losD := match si with
        | .pos _ => if losD0.any (· ≥ 1) then losD0 else losD0.push 1
        | _ => losD0
      let hisD := match si with
        | .neg _ => if hisD0.any (· ≤ -1) then hisD0 else hisD0.push (-1)
        | _ => hisD0
      -- positive divisor
      for ld in losD do
        if ld ≥ 1 then
          let hisDpos := hisD.filter (· ≥ ld)
          for hm in hisM do
            if hisDpos.isEmpty then
              let β := hm.fdiv ld
              -- tightness gate (Z3 should_propagate_*): skip bounds already
              -- implied by a mined bound on the cofactor
              if β ≥ 0 && hm < ld * (β + 1) && hisCof.all (β < ·) then
                if let some pfs := ← dischargeAll cache #[← le (mkIntLit ld) dvsr, ← le m (mkIntLit hm)] then
                  let e ← mkE
                  let h₀ ← mkDecideProof (← lt' (mkIntLit 0) (mkIntLit ld))
                  let c₀ ← mkDecideProof (← le (mkIntLit 0) (mkIntLit β))
                  let c₁ ← mkDecideProof (← lt' (mkIntLit hm) (← mulE (mkIntLit ld) (← bOff β 1)))
                  let pf ← mkAppM ``sr_down_ub_pos1 #[e, h₀, pfs[0]!, pfs[1]!, c₀, c₁]
                  out := out.push (.mkSimple s!"nla_dwn_{idx}_{out.size}", ← inferType pf, pf)
            else
              for hd in hisDpos do
                let β := max (hm.fdiv ld) (hm.fdiv hd)
                if hm < ld * (β + 1) && hm < hd * (β + 1) && hisCof.all (β < ·) then
                  if let some pfs := ← dischargeAll cache
                      #[← le (mkIntLit ld) dvsr, ← le dvsr (mkIntLit hd), ← le m (mkIntLit hm)] then
                    let e ← mkE
                    let h₀ ← mkDecideProof (← lt' (mkIntLit 0) (mkIntLit ld))
                    let c₁ ← mkDecideProof (← lt' (mkIntLit hm) (← mulE (mkIntLit ld) (← bOff β 1)))
                    let c₂ ← mkDecideProof (← lt' (mkIntLit hm) (← mulE (mkIntLit hd) (← bOff β 1)))
                    let pf ← mkAppM ``sr_down_ub_pos #[e, h₀, pfs[0]!, pfs[1]!, pfs[2]!, c₁, c₂]
                    out := out.push (.mkSimple s!"nla_dwn_{idx}_{out.size}", ← inferType pf, pf)
          for lm in losM do
            if hisDpos.isEmpty then
              let β := cdiv lm ld
              if β ≤ 0 && ld * (β - 1) < lm && losCof.all (· < β) then
                if let some pfs := ← dischargeAll cache #[← le (mkIntLit ld) dvsr, ← le (mkIntLit lm) m] then
                  let e ← mkE
                  let h₀ ← mkDecideProof (← lt' (mkIntLit 0) (mkIntLit ld))
                  let c₀ ← mkDecideProof (← le (mkIntLit β) (mkIntLit 0))
                  let c₁ ← mkDecideProof (← lt' (← mulE (mkIntLit ld) (← bOff β (-1))) (mkIntLit lm))
                  let pf ← mkAppM ``sr_down_lb_pos1 #[e, h₀, pfs[0]!, pfs[1]!, c₀, c₁]
                  out := out.push (.mkSimple s!"nla_dwn_{idx}_{out.size}", ← inferType pf, pf)
            else
              for hd in hisDpos do
                let β := min (cdiv lm ld) (cdiv lm hd)
                if ld * (β - 1) < lm && hd * (β - 1) < lm && losCof.all (· < β) then
                  if let some pfs := ← dischargeAll cache
                      #[← le (mkIntLit ld) dvsr, ← le dvsr (mkIntLit hd), ← le (mkIntLit lm) m] then
                    let e ← mkE
                    let h₀ ← mkDecideProof (← lt' (mkIntLit 0) (mkIntLit ld))
                    let c₁ ← mkDecideProof (← lt' (← mulE (mkIntLit ld) (← bOff β (-1))) (mkIntLit lm))
                    let c₂ ← mkDecideProof (← lt' (← mulE (mkIntLit hd) (← bOff β (-1))) (mkIntLit lm))
                    let pf ← mkAppM ``sr_down_lb_pos #[e, h₀, pfs[0]!, pfs[1]!, pfs[2]!, c₁, c₂]
                    out := out.push (.mkSimple s!"nla_dwn_{idx}_{out.size}", ← inferType pf, pf)
      -- negative divisor
      for hd in hisD do
        if hd ≤ -1 then
          let losDneg := losD.filter (· ≤ hd)
          for ld in losDneg do
            for lm in losM do
              let β := max (lm.fdiv ld) (lm.fdiv hd)
              if ld * (β + 1) < lm && hd * (β + 1) < lm && hisCof.all (β < ·) then
                if let some pfs := ← dischargeAll cache
                    #[← le (mkIntLit ld) dvsr, ← le dvsr (mkIntLit hd), ← le (mkIntLit lm) m] then
                  let e ← mkE
                  let h₀ ← mkDecideProof (← lt' (mkIntLit hd) (mkIntLit 0))
                  let c₁ ← mkDecideProof (← lt' (← mulE (mkIntLit ld) (← bOff β 1)) (mkIntLit lm))
                  let c₂ ← mkDecideProof (← lt' (← mulE (mkIntLit hd) (← bOff β 1)) (mkIntLit lm))
                  let pf ← mkAppM ``sr_down_ub_neg #[e, h₀, pfs[0]!, pfs[1]!, pfs[2]!, c₁, c₂]
                  out := out.push (.mkSimple s!"nla_dwn_{idx}_{out.size}", ← inferType pf, pf)
            for hm in hisM do
              let β := min (cdiv hm ld) (cdiv hm hd)
              if hm < ld * (β - 1) && hm < hd * (β - 1) && losCof.all (· < β) then
                if let some pfs := ← dischargeAll cache
                    #[← le (mkIntLit ld) dvsr, ← le dvsr (mkIntLit hd), ← le m (mkIntLit hm)] then
                  let e ← mkE
                  let h₀ ← mkDecideProof (← lt' (mkIntLit hd) (mkIntLit 0))
                  let c₁ ← mkDecideProof (← lt' (mkIntLit hm) (← mulE (mkIntLit ld) (← bOff β (-1))))
                  let c₂ ← mkDecideProof (← lt' (mkIntLit hm) (← mulE (mkIntLit hd) (← bOff β (-1))))
                  let pf ← mkAppM ``sr_down_lb_neg #[e, h₀, pfs[0]!, pfs[1]!, pfs[2]!, c₁, c₂]
                  out := out.push (.mkSimple s!"nla_dwn_{idx}_{out.size}", ← inferType pf, pf)
      -- down-sign: divisor-sign quotient of the atom's sign (nonlinear,
      -- invisible to the omega leaf); skipped when the cofactor's lattice
      -- already serves the conclusion
      let pick : Option (Name × Expr × Expr × Shape) :=
        match si, siM with
        | .pos pd, .pos pm    => some (``sr_dsign_pp, pd, pm, .pos)
        | .pos pd, .neg pm    => some (``sr_dsign_pn, pd, pm, .neg)
        | .neg pd, .pos pm    => some (``sr_dsign_np, pd, pm, .neg)
        | .neg pd, .neg pm    => some (``sr_dsign_nn, pd, pm, .pos)
        | .pos pd, .nonneg pm => some (``sr_dsign_pp', pd, pm, .nonneg)
        | .pos pd, .nonpos pm => some (``sr_dsign_pn', pd, pm, .nonpos)
        | .neg pd, .nonneg pm => some (``sr_dsign_np', pd, pm, .nonpos)
        | .neg pd, .nonpos pm => some (``sr_dsign_nn', pd, pm, .nonneg)
        | _, _ => none
      if let some (lem, pd, pm, sh) := pick then
        if (← cofSi.shapePf? sh).isNone then
          let e ← mkE
          let pf ← mkAppM lem #[e, pd, pm]
          out := out.push (.mkSimple s!"nla_dsg_{idx}_{out.size}", ← inferType pf, pf)
    return out

/-- Facts for a power monomial `a ^ k` (literal `k ≥ 2`): parity/zero/sign
rules, side conditions on the exponent by `decide`. -/
def factsForPow (cache : DCache) (m : Expr) (idx : Nat) :
    TacticM (Array (Name × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let some (a, k) := isIntPow? m | return #[]
    let mut out : Array (Name × Expr × Expr) := #[]
    let kE := mkNatLit k
    -- even exponent: unconditionally nonnegative
    if k % 2 == 0 then
      let hk ← mkDecideProof (← mkAppM ``Even #[kE])
      let pf ← mkAppM ``sr_pow_even_nonneg #[hk, a]
      out := out.push (.mkSimple s!"nla_pow_{idx}", ← inferType pf, pf)
    -- zero/sign rules read the base's lattice position; strongest rule wins
    match ← signFactsFor cache a with
    | .zero pa =>
      let hk ← mkDecideProof (← mkAppM ``Ne #[kE, mkNatLit 0])
      let pf ← mkAppM ``sr_pow_zero #[hk, pa]
      out := out.push (.mkSimple s!"nla_pow_{idx}_z", ← inferType pf, pf)
    | .pos pa =>
      let pf ← mkAppM ``sr_pow_pos #[kE, pa]
      out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .nonneg pa =>
      let pf ← mkAppM ``sr_pow_nonneg #[kE, pa]
      out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .neg pa =>
      if k % 2 == 1 then
        let hk ← mkDecideProof (← mkAppM ``Odd #[kE])
        let pf ← mkAppM ``sr_pow_odd_neg #[hk, pa]
        out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .nonpos pa =>
      if k % 2 == 1 then
        let hk ← mkDecideProof (← mkAppM ``Odd #[kE])
        let pf ← mkAppM ``sr_pow_odd_nonpos #[hk, pa]
        out := out.push (.mkSimple s!"nla_pow_{idx}_s", ← inferType pf, pf)
    | .unknown => pure ()
    -- square envelopes (RULES squares row): secant above on each mined
    -- interval, tangent below at each mined anchor; `s`/`p`/`t`/`q`
    -- pre-evaluated to literals (corner-fold rule: no unevaluated ground
    -- terms in noted facts)
    if k == 2 then
      let (los, his) ← mineBounds a
      let le (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
      for lo in los do
        for hi in his do
          let prems := #[← le (mkIntLit lo) a, ← le a (mkIntLit hi)]
          if let some pfs := ← dischargeAll cache prems then
            let hs ← mkDecideProof (← mkAppM ``Eq
              #[mkIntLit (lo + hi), ← mkAppM ``HAdd.hAdd #[mkIntLit lo, mkIntLit hi]])
            let hp ← mkDecideProof (← mkAppM ``Eq
              #[mkIntLit (lo * hi), ← mkAppM ``HMul.hMul #[mkIntLit lo, mkIntLit hi]])
            let pf ← mkAppM ``sr_sq_secant #[pfs[0]!, pfs[1]!, hs, hp]
            out := out.push (.mkSimple s!"nla_sqs_{idx}_{out.size}", ← inferType pf, pf)
      for c in (los ++ his).toList.eraseDups do
        let ht ← mkDecideProof (← mkAppM ``Eq
          #[mkIntLit (2 * c), ← mkAppM ``HMul.hMul #[mkIntLit 2, mkIntLit c]])
        let hq ← mkDecideProof (← mkAppM ``Eq
          #[mkIntLit (c * c), ← mkAppM ``HMul.hMul #[mkIntLit c, mkIntLit c]])
        let pf ← mkAppM ``sr_sq_tangent #[a, ht, hq]
        out := out.push (.mkSimple s!"nla_sqt_{idx}_{out.size}", ← inferType pf, pf)
      -- MB4/MB5 down-propagation: integer roots of atom bounds → base
      -- bounds. MB4's two conjuncts are noted separately (Z3 emits each as
      -- its own clause); MB5's conclusion is genuinely disjunctive and the
      -- omega leaf case-splits on it. Roots are floor/ceil √ in meta,
      -- certified by decide.
      let (losP, hisP) ← mineBounds m
      for u in hisP do
        if u ≥ 0 then
          let r : Int := Int.ofNat (Nat.sqrt u.toNat)
          -- tightness gate: skip roots already implied by mined base bounds
          if u < (r + 1) * (r + 1) && (his.all (r < ·) || los.all (-r < ·)) then
            if let some ph := ← tryDischarge cache (← le m (mkIntLit u)) then
              let hr ← mkDecideProof (← le (mkIntLit 0) (mkIntLit r))
              let rp1 ← mkAppM ``HAdd.hAdd #[mkIntLit r, mkIntLit 1]
              let cnd ← mkDecideProof
                (← mkAppM ``LT.lt #[mkIntLit u, ← mkAppM ``HMul.hMul #[rp1, rp1]])
              let pfHi ← mkAppM ``sr_sq_root_ub_hi #[ph, hr, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pfHi, pfHi)
              let pfLo ← mkAppM ``sr_sq_root_ub_lo #[ph, hr, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pfLo, pfLo)
      for l in losP do
        if l ≥ 1 then
          let r : Int := Int.ofNat (Nat.sqrt (l - 1).toNat + 1)
          if (r - 1) * (r - 1) < l then
            if let some ph := ← tryDischarge cache (← le (mkIntLit l) m) then
              let rm1 ← mkAppM ``HSub.hSub #[mkIntLit r, mkIntLit 1]
              let cnd ← mkDecideProof
                (← mkAppM ``LT.lt #[← mkAppM ``HMul.hMul #[rm1, rm1], mkIntLit l])
              let pf ← mkAppM ``sr_sq_root_lb #[ph, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pf, pf)
    return out

/-- Class C pair phase (RULES O2/O3): scan hypotheses for comparisons
between two product monomials sharing a factor; cancel the shared factor
when its lattice sign is known. Runs after the per-monomial loop so noted
facts participate in the scan and in the lattice probes. Rel encoding:
0 = ≤, 1 = <, 2 = = (GE/GT pre-swapped). -/
def generatePairs (cache : DCache) (noted : NotedSet) : TacticM Bool := do
  let g ← getMainGoal
  let facts ← g.withContext do
    let mut out : Array (Name × Expr × Expr) := #[]
    for decl in ← getLCtx do
      if decl.isImplementationDetail then continue
      let ty ← instantiateMVars decl.type
      let (x?, y?, rel, viaNot) :=
        match ty.getAppFnArgs with
        | (``LE.le, #[t, _, lh, rh]) =>
          if t.isConstOf ``Int then (some lh, some rh, 0, false) else (none, none, 0, false)
        | (``LT.lt, #[t, _, lh, rh]) =>
          if t.isConstOf ``Int then (some lh, some rh, 1, false) else (none, none, 0, false)
        | (``GE.ge, #[t, _, lh, rh]) =>
          if t.isConstOf ``Int then (some rh, some lh, 0, false) else (none, none, 0, false)
        | (``GT.gt, #[t, _, lh, rh]) =>
          if t.isConstOf ``Int then (some rh, some lh, 1, false) else (none, none, 0, false)
        | (``Eq, #[t, lh, rh]) =>
          if t.isConstOf ``Int then (some lh, some rh, 2, false) else (none, none, 0, false)
        | (``Not, #[p]) =>
          -- control-flow negations: ¬(l < r) ⟹ r ≤ l, ¬(l ≤ r) ⟹ r < l,
          -- GE/GT duals — Z3's LRA state holds these as bounds
          match p.getAppFnArgs with
          | (``LT.lt, #[t, _, lh, rh]) =>
            if t.isConstOf ``Int then (some rh, some lh, 0, true) else (none, none, 0, false)
          | (``LE.le, #[t, _, lh, rh]) =>
            if t.isConstOf ``Int then (some rh, some lh, 1, true) else (none, none, 0, false)
          | (``GT.gt, #[t, _, lh, rh]) =>
            if t.isConstOf ``Int then (some lh, some rh, 0, true) else (none, none, 0, false)
          | (``GE.ge, #[t, _, lh, rh]) =>
            if t.isConstOf ``Int then (some lh, some rh, 1, true) else (none, none, 0, false)
          | _ => (none, none, 0, false)
        | _ => (none, none, 0, false)
      let some x := x? | continue
      let some y := y? | continue
      let x := x.consumeMData
      let y := y.consumeMData
      if x == y then continue
      let some (x₁, x₂) := isIntMul? x | continue
      let some (y₁, y₂) := isIntMul? y | continue
      -- normalize the hyp proof to ≤/</= orientation (GE/GT are defeq
      -- through the instance; the hint makes it syntactic — slice-5 lesson).
      -- ¬-wrapped hyps go through le_of_not_gt / lt_of_not_ge.
      let hPf ←
        if viaNot then do
          let notTy ← match rel with
            | 0 => do mkAppM ``Not #[← mkAppM ``LT.lt #[y, x]]
            | _ => do mkAppM ``Not #[← mkAppM ``LE.le #[y, x]]
          let hinted ← mkExpectedTypeHint (.fvar decl.fvarId) notTy
          if rel == 0 then mkAppM ``le_of_not_gt #[hinted]
          else mkAppM ``lt_of_not_ge #[hinted]
        else do
          let relTy ← match rel with
            | 0 => mkAppM ``LE.le #[x, y]
            | 1 => mkAppM ``LT.lt #[x, y]
            | _ => mkAppM ``Eq #[x, y]
          mkExpectedTypeHint (.fvar decl.fvarId) relTy
      -- all shared-factor alignments; comm flags select Eq.refl vs mul_comm
      -- for the position-absorbing premises
      let mut combos : Array (Expr × Expr × Expr × Bool × Bool) := #[]
      if x₂ == y₂ then combos := combos.push (x₁, y₁, x₂, false, false)
      if x₂ == y₁ then combos := combos.push (x₁, y₂, x₂, false, true)
      if x₁ == y₂ then combos := combos.push (x₂, y₁, x₁, true, false)
      if x₁ == y₁ then combos := combos.push (x₂, y₂, x₁, true, true)
      for (u, v, w, comm₁, comm₂) in combos do
        let siW ← signFactsFor cache w
        let e₁ ← if comm₁ then mkAppM ``mul_comm #[w, u] else mkEqRefl x
        let e₂ ← if comm₂ then mkAppM ``mul_comm #[w, v] else mkEqRefl y
        let note? : Option Expr ← match rel, siW with
          | 0, .pos pw => some <$> mkAppM ``sr_cancel_le_pos #[e₁, e₂, pw, hPf]
          | 0, .neg pw => some <$> mkAppM ``sr_cancel_le_neg #[e₁, e₂, pw, hPf]
          | 1, .pos pw => some <$> mkAppM ``sr_cancel_lt_pos #[e₁, e₂, pw, hPf]
          | 1, .neg pw => some <$> mkAppM ``sr_cancel_lt_neg #[e₁, e₂, pw, hPf]
          | 2, .pos pw => do
            let ne ← mkAppM ``ne_of_gt #[pw]
            some <$> mkAppM ``sr_cancel_eq #[e₁, e₂, ne, hPf]
          | 2, .neg pw => do
            let ne ← mkAppM ``ne_of_lt #[pw]
            some <$> mkAppM ``sr_cancel_eq #[e₁, e₂, ne, hPf]
          | _, _ => pure none
        if let some pf := note? then
          out := out.push (.mkSimple s!"nla_cnc_{out.size}", ← inferType pf, pf)
    pure out
  let mut new := false
  for (nm, tyF, pf) in facts do
    new := (← noteFact noted nm tyF pf) || new
  return new

/-- Class D clause phase (RULES B2-conditional/B5/B6/B7/B8/O1): noted only
after a failed leaf attempt — the model-free counterpart of Z3's lazy
model-guided clause emission. Gated to monomials with a sign-unknown
factor, so the leaf's branch count tracks genuine unknowns. -/
def generateClauses (cache : DCache) (noted : NotedSet) (ms : Array Expr)
    (tier : Nat) : TacticM Unit := do
  let g ← getMainGoal
  let facts ← g.withContext do
    let mut out : Array (Name × Expr × Expr) := #[]
    for m in ms do
      let some (a, b) := isIntMul? m | continue
      let siA ← signFactsFor cache a
      let siB ← signFactsFor cache b
      let aU := !siA.isKnown
      let bU := !siB.isKnown
      if (aU || bU) && tier == 1 then
        -- tier 1: B2-conditional sign clauses + zero clauses (B6
        -- orientation) + B5 — linear disjuncts, prune fast against the
        -- context when the monomial is irrelevant to the goal
        for lem in [``sr_cl_pp, ``sr_cl_nn, ``sr_cl_pn, ``sr_cl_np,
                    ``sr_cl_zl, ``sr_cl_zr, ``sr_cl_b5] do
          let pf ← mkAppM lem #[a, b]
          out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
      if (aU || bU) && tier == 2 then
        -- tier 2 (second failure only): the branch-heavy rows. natAbs
        -- facts case-split per atom occurrence regardless of relevance,
        -- and each O1 pivot clause stays two-way live for an
        -- unconstrained cofactor — multiplicative across monomials, so
        -- they join the leaf only when tier 1 was insufficient.
        -- B7/B8 (natAbs rows): only with a discharged nonzero factor
        if let some pa := ← tryDischarge cache (← mkAppM ``Ne #[a, mkIntLit 0]) then
          let pf ← mkAppM ``sr_b8_left #[b, pa]
          out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
          let pf7 ← mkAppM ``sr_cl_b7 #[a, b]
          out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf7, pf7)
        if let some pb := ← tryDischarge cache (← mkAppM ``Ne #[b, mkIntLit 0]) then
          let pf ← mkAppM ``sr_b8_right #[a, pb]
          out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
          let pf7 ← mkAppM ``sr_cl_b7r #[a, b]
          out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf7, pf7)
        -- O1 clauses: mined pivot × sign-unknown cofactor
        let le' (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
        let (losA', hisA') ← mineBounds a
        let (losB', hisB') ← mineBounds b
        if bU then
          for pv in hisA' do
            if let some ph := ← tryDischarge cache (← le' a (mkIntLit pv)) then
              for lem in [``sr_cl_o1_ub, ``sr_cl_o1_ub'] do
                let pf ← mkAppM lem #[b, ph]
                out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
          for pv in losA' do
            if let some ph := ← tryDischarge cache (← le' (mkIntLit pv) a) then
              for lem in [``sr_cl_o1_lb, ``sr_cl_o1_lb'] do
                let pf ← mkAppM lem #[b, ph]
                out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
        if aU then
          for pv in hisB' do
            if let some ph := ← tryDischarge cache (← le' b (mkIntLit pv)) then
              for lem in [``sr_cl_o1_ubr, ``sr_cl_o1_ubr'] do
                let pf ← mkAppM lem #[a, ph]
                out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
          for pv in losB' do
            if let some ph := ← tryDischarge cache (← le' (mkIntLit pv) b) then
              for lem in [``sr_cl_o1_lbr, ``sr_cl_o1_lbr'] do
                let pf ← mkAppM lem #[a, ph]
                out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
    pure out
  for (nm, tyF, pf) in facts do
    let _ ← noteFact noted nm tyF pf

/-- Generation round: instantiate the rule vocabulary for every monomial,
inner monomials first so their facts feed outer premises; then the pair
phase over the completed context. Returns `true` iff any new fact was
noted — the multi-round fixpoint signal. -/
def generate (cache : DCache) (noted : NotedSet) (ms : Array Expr) :
    TacticM Bool := do
  let mut idx := 0
  let mut new := false
  for m in ms do
    let facts ← if (isIntMul? m).isSome then factsFor cache m idx
                else factsForPow cache m idx
    let mut notedHere := false
    for (nm, ty, pf) in facts do
      notedHere := (← noteFact noted nm ty pf) || notedHere
    if notedHere then
      -- the context grew: failed discharges may now succeed, so drop
      -- negative entries; positive proofs stay valid (fvars persist)
      cache.modify (·.filter fun _ v => v.isSome)
      new := true
    idx := idx + 1
  let pairsNew ← generatePairs cache noted
  return new || pairsNew

def saturateCore (stats : Bool := false) (maxRounds : Nat := 3) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  -- 0. normalize: sum-of-monomials form; doubles as commutative canonization
  evalTactic (← `(tactic| try ring_nf at *))
  if (← getGoals).isEmpty then return
  let t1 ← IO.monoMsNow
  -- 1. collect from hypotheses and goal
  let g ← getMainGoal
  let ms ← g.withContext do
    let act : StateRefT (Array Expr) MetaM Unit := do
      for fv in ← g.getNondepPropHyps do
        collectMonomials (← fv.getType)
      collectMonomials (← g.getType)
    let ((), ms) ← act.run #[]
    pure ms
  -- 2. generate: bounded rounds to fixpoint. A single sequential pass is
  -- order-dependent (Gauss-Seidel: facts noted for monomial i feed only
  -- monomials j > i in the ring_nf-determined context order); Z3's
  -- saturation is fixpoint-driven — the final-check loop re-enters nla
  -- until no new lemmas fire. Rounds + noted-set dedup remove the order
  -- dependence; `maxRounds` bounds tightening chains (down-prop β values
  -- strictly tighten each pass, so adversarial goals could iterate long —
  -- the containment statement is per-round-count, mirroring Z3's own
  -- resource bound). The monomial set is stable across rounds: every
  -- generator conclusion is over the already-collected vocabulary.
  let cache : DCache ← IO.mkRef {}
  let noted : NotedSet ← IO.mkRef {}
  let g ← getMainGoal
  g.withContext do
    for fv in ← g.getNondepPropHyps do
      noted.modify (·.insert (← instantiateMVars (← fv.getType)).consumeMData)
  let mut rounds := 0
  for _ in [0:max 1 maxRounds] do
    let progress ← generate cache noted ms
    rounds := rounds + 1
    if !progress then break
  let t2 ← IO.monoMsNow
  -- 3. leaf: omega atomizes the (ring_nf-canonized) monomials natively —
  -- no explicit generalization needed; SaturateTests pins this assumption.
  -- On failure: class D failure-gated clause phase (Z3's lazy clause
  -- emission, model-free) — roll back, note conditional clauses, retry.
  let s ← saveState
  let retried ← try
    evalTactic (← `(tactic| omega))
    pure 0
  catch _ =>
    restoreState s
    generateClauses cache noted ms 1
    let s2 ← saveState
    try
      evalTactic (← `(tactic| omega))
      pure 1
    catch _ =>
      restoreState s2
      generateClauses cache noted ms 2
      evalTactic (← `(tactic| omega))
      pure 2
  let t3 ← IO.monoMsNow
  if stats then
    logInfo s!"nla_saturate: ring_nf {t1 - t0}ms · generate {t2 - t1}ms \
      ({ms.size} monomials, {rounds} rounds, {← nlaTacticCall.get} tactic calls, \
      {← nlaCacheHit.get} cache hits, {← nlaLitFast.get} literal fast) \
      · omega {t3 - t2}ms{if retried > 0 then s!" (clause retry tier {retried})" else ""}"

/-- `nla_saturate (n)?` — optional numeral overrides the round bound
(default 3). -/
elab "nla_saturate" n:(num)? : tactic =>
  saturateCore (maxRounds := n.map (·.getNat) |>.getD 3)

/-- `nla_saturate` with phase timings and discharge-oracle counters. -/
elab "nla_saturate_stats" n:(num)? : tactic => do
  nlaLitFast.set 0; nlaCacheHit.set 0; nlaTacticCall.set 0
  saturateCore (stats := true) (maxRounds := n.map (·.getNat) |>.getD 3)

end LeanNonlinearArith.Tactic
