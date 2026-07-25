import Mathlib
import LeanNonlinearArith.Templates.Intervals
import LeanNonlinearArith.Templates.Divisions
import LeanNonlinearArith.Templates.Tangent
import LeanNonlinearArith.Tactic.Oracle

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

/- Division/modulo rules (RULES rows D4/D5 + the div/mod axiomatization Z3's
core solver asserts for every div/mod term). Only symbolic divisors get
rules — literal divisors are omega-native at the leaf. `sr_divmod_def` is
the defining equation; its product `y * (x / y)` joins the monomial set so
the full product machinery runs on it. -/
theorem sr_divmod_def (x y : ℤ) : y * (x / y) + x % y = x :=
  Int.mul_ediv_add_emod x y
-- both orientations are noted: ring_nf canonizes user-written products of
-- `y` and `x / y` to ITS order, which need not match the meta-built form —
-- omega atomizes them separately, so each orientation needs its own bridge
-- (probe-confirmed: `(x/y) * y ≤ 5 → x - x % y ≤ 5` failed one-sided)
theorem sr_divmod_def' (x y : ℤ) : x / y * y + x % y = x := by
  rw [mul_comm]; exact Int.mul_ediv_add_emod x y
theorem sr_mod_lb (x : ℤ) {y : ℤ} (h : y ≠ 0) : 0 ≤ x % y :=
  Int.emod_nonneg x h
theorem sr_mod_ub_pos (x : ℤ) {y : ℤ} (h : 0 < y) : x % y < y :=
  Int.emod_lt_of_pos x h
theorem sr_mod_ub_neg (x : ℤ) {y : ℤ} (h : y < 0) : x % y < -y := by
  rw [← Int.emod_neg]; exact Int.emod_lt_of_pos x (by omega)
theorem sr_div_subst (x : ℤ) {y c : ℤ} (h : y = c) : x / y = x / c := by
  rw [h]
theorem sr_mod_subst (x : ℤ) {y c : ℤ} (h : y = c) : x % y = x % c := by
  rw [h]

/- k ≥ 3 power rules (RULES rows MB1-2/MB4/MB5 at general exponents — Z3's
monomial_bounds interval powers and root propagation are k-generic).
Conclusions carry pre-evaluated literals (corner-fold rule); the `hc`/`cnd`
equalities and comparisons are decide-certified at generation time. Root
lemmas are contrapositive forms mirroring the k = 2 `u < (r+1)²` pattern. -/
theorem sr_pow_ub_odd {a : ℤ} {p : ℕ} (hp : Odd p) {hi c : ℤ}
    (h : a ≤ hi) (hc : hi ^ p = c) : a ^ p ≤ c :=
  hc ▸ hp.pow_le_pow.mpr h
theorem sr_pow_lb_odd {a : ℤ} {p : ℕ} (hp : Odd p) {lo c : ℤ}
    (h : lo ≤ a) (hc : lo ^ p = c) : c ≤ a ^ p :=
  hc ▸ hp.pow_le_pow.mpr h
theorem sr_pow_ub_even {a : ℤ} {p : ℕ} (hp : Even p) {lo hi M c : ℤ}
    (h1 : lo ≤ a) (h2 : a ≤ hi) (hlo : -M ≤ lo) (hhi : hi ≤ M)
    (hc : M ^ p = c) : a ^ p ≤ c := by
  have habs : |a| ≤ M := abs_le.mpr ⟨by omega, by omega⟩
  calc a ^ p = |a| ^ p := (hp.pow_abs a).symm
    _ ≤ M ^ p := pow_le_pow_left₀ (abs_nonneg a) habs p
    _ = c := hc
theorem sr_pow_lb_even_pos {a : ℤ} {p : ℕ} {lo c : ℤ}
    (h0 : 0 ≤ lo) (h : lo ≤ a) (hc : lo ^ p = c) : c ≤ a ^ p :=
  hc ▸ pow_le_pow_left₀ h0 h p
theorem sr_pow_lb_even_neg {a : ℤ} {p : ℕ} (hp : Even p) {hi c : ℤ}
    (h0 : hi ≤ 0) (h : a ≤ hi) (hc : (-hi) ^ p = c) : c ≤ a ^ p := by
  have habs : -hi ≤ |a| := (neg_le_neg h).trans (neg_le_abs a)
  calc c = (-hi) ^ p := hc.symm
    _ ≤ |a| ^ p := pow_le_pow_left₀ (by omega) habs p
    _ = a ^ p := hp.pow_abs a
theorem sr_pow_root_ub_odd {v : ℤ} {p : ℕ} (hp : Odd p) {u r : ℤ}
    (h : v ^ p ≤ u) (cnd : u < (r + 1) ^ p) : v ≤ r := by
  by_contra hcon
  push_neg at hcon
  have : (r + 1) ^ p ≤ v ^ p := hp.pow_le_pow.mpr (by omega)
  omega
theorem sr_pow_root_ub_even_hi {v : ℤ} {p : ℕ} {u r : ℤ}
    (hr : 0 ≤ r) (h : v ^ p ≤ u) (cnd : u < (r + 1) ^ p) : v ≤ r := by
  by_contra hcon
  push_neg at hcon
  -- `hr` used explicitly (the lemma is false for r < -1); omega-internal
  -- uses are invisible to the unused-variable lint
  have : (r + 1) ^ p ≤ v ^ p :=
    pow_le_pow_left₀ (add_nonneg hr zero_le_one) (by omega) p
  omega
theorem sr_pow_root_ub_even_lo {v : ℤ} {p : ℕ} (hp : Even p) {u r : ℤ}
    (hr : 0 ≤ r) (h : v ^ p ≤ u) (cnd : u < (r + 1) ^ p) : -r ≤ v := by
  by_contra hcon
  push_neg at hcon
  have h1 : (r + 1) ^ p ≤ (-v) ^ p :=
    pow_le_pow_left₀ (add_nonneg hr zero_le_one) (by omega) p
  rw [hp.neg_pow] at h1
  omega
theorem sr_pow_root_lb_odd {v : ℤ} {p : ℕ} (hp : Odd p) {l r : ℤ}
    (h : l ≤ v ^ p) (cnd : (r - 1) ^ p < l) : r ≤ v := by
  by_contra hcon
  push_neg at hcon
  have : v ^ p ≤ (r - 1) ^ p := hp.pow_le_pow.mpr (by omega)
  omega
-- no `1 ≤ r` premise needed: for r ≤ 0 the disjunction is a tautology, and
-- the contradiction branch derives r ≥ 1 from -r < v < r on its own
theorem sr_pow_root_lb_even {v : ℤ} {p : ℕ} (hp : Even p) {l r : ℤ}
    (h : l ≤ v ^ p) (cnd : (r - 1) ^ p < l) : r ≤ v ∨ v ≤ -r := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  have habs : |v| ≤ r - 1 := abs_le.mpr ⟨by omega, by omega⟩
  have : v ^ p ≤ (r - 1) ^ p := by
    calc v ^ p = |v| ^ p := (hp.pow_abs v).symm
      _ ≤ (r - 1) ^ p := pow_le_pow_left₀ (abs_nonneg v) habs p
  omega

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

/- O4 — ±-equivalence rows (RULES O4, Z3 `generate_mon_ol` :163 + emonics
canonization modulo `evars`). The oracle's parity union-find derives unit
±-equalities the spelling never shows; these lemmas carry them to product
level. Eager bridges (both factor pairs equivalent) are case-free
equalities — Z3 identifies such monomials structurally in its table. The
clause forms (one equivalent factor pair, cofactors free) are the
model-free closure of Z3's sign-selected order-transfer clause
`c_sign·c ≤ 0 ∨ ¬(c_sign·a ⋈ d_sign·b) ∨ ac ⋈ bd`. `ep`/`eq'` absorb
factor positions (`Eq.refl` or `mul_comm`), as in the Cancel section. -/
section O4
variable {a b c d p q : ℤ} {k : ℕ}

theorem sr_o4_mul_pp (e₁ : b = a) (e₂ : d = c)
    (ep : p = a * c) (eq' : q = b * d) : q = p := by
  subst e₁; subst e₂; subst ep; subst eq'; rfl
theorem sr_o4_mul_pn (e₁ : b = a) (e₂ : d = -c)
    (ep : p = a * c) (eq' : q = b * d) : q = -p := by
  subst e₁; subst e₂; subst ep; subst eq'; ring
theorem sr_o4_mul_np (e₁ : b = -a) (e₂ : d = c)
    (ep : p = a * c) (eq' : q = b * d) : q = -p := by
  subst e₁; subst e₂; subst ep; subst eq'; ring
theorem sr_o4_mul_nn (e₁ : b = -a) (e₂ : d = -c)
    (ep : p = a * c) (eq' : q = b * d) : q = p := by
  subst e₁; subst e₂; subst ep; subst eq'; ring

theorem sr_o4_pow_p (e : d = c) (ep : p = c ^ k) (eq' : q = d ^ k) :
    q = p := by subst e; subst ep; subst eq'; rfl
theorem sr_o4_pow_even (hk : Even k) (e : d = -c)
    (ep : p = c ^ k) (eq' : q = d ^ k) : q = p := by
  subst e; subst ep; subst eq'; exact hk.neg_pow c
theorem sr_o4_pow_odd (hk : Odd k) (e : d = -c)
    (ep : p = c ^ k) (eq' : q = d ^ k) : q = -p := by
  subst e; subst ep; subst eq'; exact hk.neg_pow c

-- (`subst e` eliminates the RHS variable `c`, so the scripts argue in `d`)
theorem sr_o4_eq_lt (e : d = c) (ep : p = a * c) (eq' : q = b * d) :
    c ≤ 0 ∨ b ≤ a ∨ p < q := by
  subst e; subst ep; subst eq'
  rcases le_or_gt d 0 with h | h
  · exact Or.inl h
  rcases le_or_gt b a with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_lt_mul_of_pos_right h' h))
theorem sr_o4_eq_gt (e : d = c) (ep : p = a * c) (eq' : q = b * d) :
    c ≤ 0 ∨ a ≤ b ∨ q < p := by
  subst e; subst ep; subst eq'
  rcases le_or_gt d 0 with h | h
  · exact Or.inl h
  rcases le_or_gt a b with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_lt_mul_of_pos_right h' h))
theorem sr_o4_eq_lt' (e : d = c) (ep : p = a * c) (eq' : q = b * d) :
    0 ≤ c ∨ b ≤ a ∨ q < p := by
  subst e; subst ep; subst eq'
  rcases le_or_gt 0 d with h | h
  · exact Or.inl h
  rcases le_or_gt b a with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_lt_mul_of_neg_right h' h))
theorem sr_o4_eq_gt' (e : d = c) (ep : p = a * c) (eq' : q = b * d) :
    0 ≤ c ∨ a ≤ b ∨ p < q := by
  subst e; subst ep; subst eq'
  rcases le_or_gt 0 d with h | h
  · exact Or.inl h
  rcases le_or_gt a b with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (mul_lt_mul_of_neg_right h' h))

theorem sr_o4_neg_lt (e : d = -c) (ep : p = a * c) (eq' : q = b * d) :
    c ≤ 0 ∨ 0 ≤ a + b ∨ p < q := by
  subst e; subst ep; subst eq'
  rcases le_or_gt c 0 with h | h
  · exact Or.inl h
  rcases le_or_gt 0 (a + b) with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (by nlinarith [mul_neg_of_neg_of_pos h' h]))
theorem sr_o4_neg_gt (e : d = -c) (ep : p = a * c) (eq' : q = b * d) :
    c ≤ 0 ∨ a + b ≤ 0 ∨ q < p := by
  subst e; subst ep; subst eq'
  rcases le_or_gt c 0 with h | h
  · exact Or.inl h
  rcases le_or_gt (a + b) 0 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (by nlinarith [mul_pos h' h]))
theorem sr_o4_neg_lt' (e : d = -c) (ep : p = a * c) (eq' : q = b * d) :
    0 ≤ c ∨ 0 ≤ a + b ∨ q < p := by
  subst e; subst ep; subst eq'
  rcases le_or_gt 0 c with h | h
  · exact Or.inl h
  rcases le_or_gt 0 (a + b) with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (by nlinarith [mul_pos_of_neg_of_neg h' h]))
theorem sr_o4_neg_gt' (e : d = -c) (ep : p = a * c) (eq' : q = b * d) :
    0 ≤ c ∨ a + b ≤ 0 ∨ p < q := by
  subst e; subst ep; subst eq'
  rcases le_or_gt 0 c with h | h
  · exact Or.inl h
  rcases le_or_gt (a + b) 0 with h' | h'
  · exact Or.inr (Or.inl h')
  exact Or.inr (Or.inr (by nlinarith [mul_neg_of_pos_of_neg h' h]))

end O4

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

/-- Binary-search worker for `natFloorRoot`: invariant `lo ^ k ≤ u`. Fueled
(the range halves each step, so `log2 u + 2` suffices) — a broken invariant
degrades to a loose-but-sound answer instead of a hang. -/
def natFloorRootGo (u k : Nat) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo ≥ hi then lo
    else
      let mid := (lo + hi + 1) / 2
      if mid ^ k ≤ u then natFloorRootGo u k fuel mid hi
      else natFloorRootGo u k fuel lo (mid - 1)

/-- Largest `r` with `r ^ k ≤ u` (`k ≥ 1`). -/
def natFloorRoot (u k : Nat) : Nat := natFloorRootGo u k (u.log2 + 2) 0 u

/-- Smallest `r` with `u ≤ r ^ k`. -/
def natCeilRoot (u k : Nat) : Nat :=
  let s := natFloorRoot u k
  if s ^ k == u then s else s + 1

/-- Largest `r : ℤ` with `r ^ k ≤ u`, for odd `k` (any sign of `u`). -/
def intFloorRootOdd (u : Int) (k : Nat) : Int :=
  if 0 ≤ u then .ofNat (natFloorRoot u.toNat k)
  else -(.ofNat (natCeilRoot (-u).toNat k))

/-- Smallest `r : ℤ` with `u ≤ r ^ k`, for odd `k` (any sign of `u`). -/
def intCeilRootOdd (u : Int) (k : Nat) : Int :=
  if 0 ≤ u then .ofNat (natCeilRoot u.toNat k)
  else -(.ofNat (natFloorRoot (-u).toNat k))

/-- Destructure an `ℤ` Euclidean division or modulo with a NON-literal
divisor (literal divisors are omega-native at the leaf and need no rules). -/
def isIntDivMod? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``HDiv.hDiv, #[ty, _, _, _, x, y]) =>
    if ty.isConstOf ``Int && !isIntLit y then some (x, y) else none
  | (``HMod.hMod, #[ty, _, _, _, x, y]) =>
    if ty.isConstOf ``Int && !isIntLit y then some (x, y) else none
  | _ => none

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

/-- Collect `(dividend, divisor)` pairs of `ℤ` div/mod terms with symbolic
divisors (both `/` and `%` map to the same pair — the rules are per pair). -/
partial def collectDivPairs (e : Expr) : StateRefT (Array (Expr × Expr)) MetaM Unit := do
  match e with
  | .app .. => do
    for arg in e.getAppArgs do
      collectDivPairs arg
    if !e.hasLooseBVars then
      if let some (x, y) := isIntDivMod? e then
        let acc ← get
        if !acc.contains (x, y) then
          modify (·.push (x, y))
  | .mdata _ b => collectDivPairs b
  | .forallE _ d b _ => collectDivPairs d; collectDivPairs b
  | .lam _ d b _ => collectDivPairs d; collectDivPairs b
  | .letE _ t v b _ => collectDivPairs t; collectDivPairs v; collectDivPairs b
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
    -- oracle v1 (DESIGN-discharge-oracle §2b/§3): derived-bound closure of
    -- the linear hypotheses; its tightest bounds join every mined-anchor
    -- set below (Z3 reads anchors from the LRA solver's propagated column
    -- bounds, not the asserted formulas — parity-restoring, and purely
    -- additive so containment-safe). Untrusted: every suggested anchor
    -- still passes through the omega discharge before instantiation.
    let oc ← runOracle
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
    -- order rules with mined constants (O1/M1-style bound propagation);
    -- oracle-derived bounds join the anchor sets
    let (losA, hisA) := oc.augment a (← mineBounds a)
    let (losB, hisB) := oc.augment b (← mineBounds b)
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
    let (losM, hisM) := oc.augment m (← mineBounds m)
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
    let oc ← runOracle
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
      let (los, his) := oc.augment a (← mineBounds a)
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
      let (losP, hisP) := oc.augment m (← mineBounds m)
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
    -- k ≥ 3: interval-pow envelopes + MB4/MB5 roots at general exponents
    -- (Z3's monomial_bounds interval powers are k-generic; k = 2 keeps its
    -- tighter secant/tangent path above). All emitted constants are
    -- pre-evaluated literals; exactness conditions decide-certified.
    if k ≥ 3 then
      let (los, his) := oc.augment a (← mineBounds a)
      let le (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
      let odd := k % 2 == 1
      let hkP? : Option Expr ←
        if odd then some <$> mkDecideProof (← mkAppM ``Odd #[kE])
        else some <$> mkDecideProof (← mkAppM ``Even #[kE])
      let hk := hkP?.get!
      let powLit (b : Int) : MetaM Expr :=
        mkAppM ``HPow.hPow #[mkIntLit b, kE]
      -- interval-pow envelopes
      if odd then
        for hi in his do
          if let some ph := ← tryDischarge cache (← le a (mkIntLit hi)) then
            let hc ← mkDecideProof (← mkAppM ``Eq #[← powLit hi, mkIntLit (hi ^ k)])
            let pf ← mkAppM ``sr_pow_ub_odd #[hk, ph, hc]
            out := out.push (.mkSimple s!"nla_pev_{idx}_{out.size}", ← inferType pf, pf)
        for lo in los do
          if let some ph := ← tryDischarge cache (← le (mkIntLit lo) a) then
            let hc ← mkDecideProof (← mkAppM ``Eq #[← powLit lo, mkIntLit (lo ^ k)])
            let pf ← mkAppM ``sr_pow_lb_odd #[hk, ph, hc]
            out := out.push (.mkSimple s!"nla_pev_{idx}_{out.size}", ← inferType pf, pf)
      else
        for lo in los do
          for hi in his do
            if let some pfs := ← dischargeAll cache
                #[← le (mkIntLit lo) a, ← le a (mkIntLit hi)] then
              let M : Int := .ofNat (max lo.natAbs hi.natAbs)
              let hlo ← mkDecideProof
                (← le (← mkAppM ``Neg.neg #[mkIntLit M]) (mkIntLit lo))
              let hhi ← mkDecideProof (← le (mkIntLit hi) (mkIntLit M))
              let hc ← mkDecideProof (← mkAppM ``Eq #[← powLit M, mkIntLit (M ^ k)])
              let pf ← mkAppM ``sr_pow_ub_even #[hk, pfs[0]!, pfs[1]!, hlo, hhi, hc]
              out := out.push (.mkSimple s!"nla_pev_{idx}_{out.size}", ← inferType pf, pf)
        for lo in los do
          if lo ≥ 0 then
            if let some ph := ← tryDischarge cache (← le (mkIntLit lo) a) then
              let h0 ← mkDecideProof (← le (mkIntLit 0) (mkIntLit lo))
              let hc ← mkDecideProof (← mkAppM ``Eq #[← powLit lo, mkIntLit (lo ^ k)])
              let pf ← mkAppM ``sr_pow_lb_even_pos #[h0, ph, hc]
              out := out.push (.mkSimple s!"nla_pev_{idx}_{out.size}", ← inferType pf, pf)
        for hi in his do
          if hi ≤ 0 then
            if let some ph := ← tryDischarge cache (← le a (mkIntLit hi)) then
              let h0 ← mkDecideProof (← le (mkIntLit hi) (mkIntLit 0))
              let negHi ← mkAppM ``Neg.neg #[mkIntLit hi]
              let hc ← mkDecideProof (← mkAppM ``Eq
                #[← mkAppM ``HPow.hPow #[negHi, kE], mkIntLit ((-hi) ^ k)])
              let pf ← mkAppM ``sr_pow_lb_even_neg #[hk, h0, ph, hc]
              out := out.push (.mkSimple s!"nla_pev_{idx}_{out.size}", ← inferType pf, pf)
      -- MB4/MB5 roots
      let (losP, hisP) := oc.augment m (← mineBounds m)
      for u in hisP do
        if odd then
          let r := intFloorRootOdd u k
          if his.all (r < ·) then
            if let some ph := ← tryDischarge cache (← le m (mkIntLit u)) then
              let rp1 ← mkAppM ``HPow.hPow
                #[← mkAppM ``HAdd.hAdd #[mkIntLit r, mkIntLit 1], kE]
              let cnd ← mkDecideProof (← mkAppM ``LT.lt #[mkIntLit u, rp1])
              let pf ← mkAppM ``sr_pow_root_ub_odd #[hk, ph, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pf, pf)
        else if u ≥ 0 then
          let r : Int := .ofNat (natFloorRoot u.toNat k)
          if his.all (r < ·) || los.all (-r < ·) then
            if let some ph := ← tryDischarge cache (← le m (mkIntLit u)) then
              let hr ← mkDecideProof (← le (mkIntLit 0) (mkIntLit r))
              let rp1 ← mkAppM ``HPow.hPow
                #[← mkAppM ``HAdd.hAdd #[mkIntLit r, mkIntLit 1], kE]
              let cnd ← mkDecideProof (← mkAppM ``LT.lt #[mkIntLit u, rp1])
              let pfHi ← mkAppM ``sr_pow_root_ub_even_hi #[hr, ph, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pfHi, pfHi)
              let pfLo ← mkAppM ``sr_pow_root_ub_even_lo #[hk, hr, ph, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pfLo, pfLo)
      for l in losP do
        if odd then
          let r := intCeilRootOdd l k
          if los.all (· < r) then
            if let some ph := ← tryDischarge cache (← le (mkIntLit l) m) then
              let rm1 ← mkAppM ``HPow.hPow
                #[← mkAppM ``HSub.hSub #[mkIntLit r, mkIntLit 1], kE]
              let cnd ← mkDecideProof (← mkAppM ``LT.lt #[rm1, mkIntLit l])
              let pf ← mkAppM ``sr_pow_root_lb_odd #[hk, ph, cnd]
              out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pf, pf)
        else if l ≥ 1 then
          let r : Int := .ofNat (natCeilRoot l.toNat k)
          if let some ph := ← tryDischarge cache (← le (mkIntLit l) m) then
            let rm1 ← mkAppM ``HPow.hPow
              #[← mkAppM ``HSub.hSub #[mkIntLit r, mkIntLit 1], kE]
            let cnd ← mkDecideProof (← mkAppM ``LT.lt #[rm1, mkIntLit l])
            let pf ← mkAppM ``sr_pow_root_lb_even #[hk, ph, cnd]
            out := out.push (.mkSimple s!"nla_rt_{idx}_{out.size}", ← inferType pf, pf)
    return out

/-- Facts for a div/mod pair `(x, y)` with symbolic divisor `y` (RULES rows
D4/D5 + the div/mod axiomatization Z3's core asserts per term):
* the defining equation `y * (x / y) + x % y = x` — its product joins the
  monomial set, so the product machinery reasons about the quotient;
* mod range, gated on the divisor's lattice sign (Euclidean: remainder is
  nonnegative for any nonzero divisor, bounded by `y` resp. `-y`);
* const-substitution at a point-mined divisor — the D4/D5 `y = yv` anchor,
  collapsed to an omega-native literal-divisor term;
* D4/D5 interval-quotient bounds at mined constants: candidate `q` computed
  by Euclidean interval division in meta, premises discharged by the oracle
  (`y * q` has a literal `q`, so they are omega-linear) — a wrong `q`
  formula can only fail to note; soundness rides on the template lemmas. -/
def factsForDiv (cache : DCache) (x y : Expr) (idx : Nat) :
    TacticM (Array (Name × Expr × Expr)) := do
  let g ← getMainGoal
  g.withContext do
    let oc ← runOracle
    let mut out : Array (Name × Expr × Expr) := #[]
    let le (u v : Expr) : MetaM Expr := mkAppM ``LE.le #[u, v]
    -- defining equation, unconditional, both product orientations (the
    -- context's ring_nf-canonized product may use either atom form)
    let pfDef ← mkAppM ``sr_divmod_def #[x, y]
    out := out.push (.mkSimple s!"nla_dvd_{idx}", ← inferType pfDef, pfDef)
    let pfDef' ← mkAppM ``sr_divmod_def' #[x, y]
    out := out.push (.mkSimple s!"nla_dvd_{idx}", ← inferType pfDef', pfDef')
    -- mod range by divisor lattice sign
    let siY ← signFactsFor cache y
    let mut divisorPos : Option Expr := none
    match siY with
    | .pos py =>
      divisorPos := some py
      let pfLb ← mkAppM ``sr_mod_lb #[x, ← mkAppM ``ne_of_gt #[py]]
      out := out.push (.mkSimple s!"nla_dvm_{idx}_{out.size}", ← inferType pfLb, pfLb)
      let pfUb ← mkAppM ``sr_mod_ub_pos #[x, py]
      out := out.push (.mkSimple s!"nla_dvm_{idx}_{out.size}", ← inferType pfUb, pfUb)
    | .neg ny =>
      let pfLb ← mkAppM ``sr_mod_lb #[x, ← mkAppM ``ne_of_lt #[ny]]
      out := out.push (.mkSimple s!"nla_dvm_{idx}_{out.size}", ← inferType pfLb, pfLb)
      let pfUb ← mkAppM ``sr_mod_ub_neg #[x, ny]
      out := out.push (.mkSimple s!"nla_dvm_{idx}_{out.size}", ← inferType pfUb, pfUb)
    | .zero pz =>
      -- degenerate divisor: substitute to the literal (x / 0 and x % 0 are
      -- omega-native)
      let pfD ← mkAppM ``sr_div_subst #[x, pz]
      out := out.push (.mkSimple s!"nla_dvs_{idx}_{out.size}", ← inferType pfD, pfD)
      let pfM ← mkAppM ``sr_mod_subst #[x, pz]
      out := out.push (.mkSimple s!"nla_dvs_{idx}_{out.size}", ← inferType pfM, pfM)
    | _ =>
      -- lattice inconclusive: a discharged `y ≠ 0` still gives the remainder
      -- lower bound
      if let some pne := ← tryDischarge cache (← mkAppM ``Ne #[y, mkIntLit 0]) then
        let pfLb ← mkAppM ``sr_mod_lb #[x, pne]
        out := out.push (.mkSimple s!"nla_dvm_{idx}_{out.size}", ← inferType pfLb, pfLb)
    -- const-substitution at a point-mined divisor (oracle-derived pins
    -- count: lb = ub from the closure is Z3's fixed-var case)
    let (lys, hys) := oc.augment y (← mineBounds y)
    for c in lys do
      if hys.contains c then
        if let some pfs := ← dischargeAll cache #[← le (mkIntLit c) y, ← le y (mkIntLit c)] then
          let pfEq ← mkAppM ``le_antisymm #[pfs[1]!, pfs[0]!]
          let pfD ← mkAppM ``sr_div_subst #[x, pfEq]
          out := out.push (.mkSimple s!"nla_dvs_{idx}_{out.size}", ← inferType pfD, pfD)
          let pfM ← mkAppM ``sr_mod_subst #[x, pfEq]
          out := out.push (.mkSimple s!"nla_dvs_{idx}_{out.size}", ← inferType pfM, pfM)
    -- D4/D5 interval-quotient bounds (positive divisor, as in
    -- nla_divisions.cpp :190/:197)
    if let some py := divisorPos then
      let (lxs, hxs) := oc.augment x (← mineBounds x)
      let lysP := lys.filter (· ≥ 1)
      let hysP := hys.filter (· ≥ 1)
      -- D4 upper: x ≤ hx → x/y ≤ q with q = hx/ly (hx ≥ 0) or hx/hy (hx < 0)
      let mut qhis : Array Int := #[]
      for hx in hxs do
        if hx ≥ 0 then
          for ly in lysP do qhis := qhis.push (hx / ly)
        else
          for hy in hysP do qhis := qhis.push (hx / hy)
      let mut seen : Array Int := #[]
      for q in qhis do
        if !seen.contains q then
          seen := seen.push q
          let qE := mkIntLit q
          let rhs ← mkAppM ``HSub.hSub
            #[← mkAppM ``HAdd.hAdd #[← mkAppM ``HMul.hMul #[y, qE], y], mkIntLit 1]
          if let some pfPrem := ← tryDischarge cache (← le x rhs) then
            let pf ← mkAppM ``Templates.Divisions.ediv_le_of_le #[x, qE, y, py, pfPrem]
            out := out.push (.mkSimple s!"nla_dv4_{idx}_{out.size}", ← inferType pf, pf)
      -- D5 lower: lx ≤ x → q ≤ x/y with q = lx/hy or 0 (lx ≥ 0), lx/ly (lx < 0)
      let mut qlos : Array Int := #[]
      for lx in lxs do
        if lx ≥ 0 then
          qlos := qlos.push 0
          for hy in hysP do qlos := qlos.push (lx / hy)
        else
          for ly in lysP do qlos := qlos.push (lx / ly)
      seen := #[]
      for q in qlos do
        if !seen.contains q then
          seen := seen.push q
          let qE := mkIntLit q
          let lhs ← mkAppM ``HMul.hMul #[y, qE]
          if let some pfPrem := ← tryDischarge cache (← le lhs x) then
            let pf ← mkAppM ``Templates.Divisions.le_ediv_of_ge #[x, qE, y, py, pfPrem]
            out := out.push (.mkSimple s!"nla_dv5_{idx}_{out.size}", ← inferType pf, pf)
    return out

/-- O4 eager bridges (Z3's emonics canonization modulo `evars`): collected
monomial pairs whose factors are pairwise ±-equivalent — equivalences the
oracle derives from unit ±-equalities — are identified up to sign. The
product-level equality `q = ±p` is case-free and linear in the two atoms,
so it goes to the eager layer, exactly as Z3 identifies such monomials
structurally in its table rather than emitting lemmas about them. Pow
pairs at the same exponent bridge through parity. -/
def generateEquivBridges (cache : DCache) (noted : NotedSet) (ms : Array Expr) :
    TacticM Bool := do
  let g ← getMainGoal
  let facts ← g.withContext do
    let oc ← runOracle
    -- ±-relation between two spellings (`some true` equal, `some false`
    -- negated); syntactic equality is the trivial case
    let relOf (u v : Expr) : Option Bool :=
      if u == v then some true else oc.pmEquiv u v
    -- equality-premise proof `u = ±v`: refl when syntactic, else the
    -- discharge oracle (omega — the equality is linear and derived)
    let relPf (u v : Expr) (sgn : Bool) : TacticM (Option Expr) := do
      if sgn && u == v then return some (← mkEqRefl u)
      let rhs ← if sgn then pure v else mkAppM ``Neg.neg #[v]
      tryDischarge cache (← mkAppM ``Eq #[u, rhs])
    let mut out : Array (Name × Expr × Expr) := #[]
    for i in [0:ms.size] do
      for j in [i+1:ms.size] do
        let p := ms[i]!
        let q := ms[j]!
        -- pow pairs at the same exponent
        if let (some (c, kp), some (d, kq)) := (isIntPow? p, isIntPow? q) then
          if kp == kq then
            if let some sgn := relOf d c then
              if let some ePf := ← relPf d c sgn then
                let epPf ← mkEqRefl p
                let eqPf ← mkEqRefl q
                let kE := mkNatLit kp
                let pf? : Option Expr ← do
                  if sgn then
                    some <$> mkAppM ``sr_o4_pow_p #[ePf, epPf, eqPf]
                  else if kp % 2 == 0 then do
                    let hk ← mkDecideProof (← mkAppM ``Even #[kE])
                    some <$> mkAppM ``sr_o4_pow_even #[hk, ePf, epPf, eqPf]
                  else do
                    let hk ← mkDecideProof (← mkAppM ``Odd #[kE])
                    some <$> mkAppM ``sr_o4_pow_odd #[hk, ePf, epPf, eqPf]
                if let some pf := pf? then
                  out := out.push (.mkSimple s!"nla_o4_{out.size}", ← inferType pf, pf)
        -- mul pairs: two alignments, first that works wins (the bridge is
        -- an equality — it fully determines the pair's relation)
        if let (some (x₁, x₂), some (y₁, y₂)) := (isIntMul? p, isIntMul? q) then
          for (b', d', comm) in #[(y₁, y₂, false), (y₂, y₁, true)] do
            let some s₁ := relOf b' x₁ | continue
            let some s₂ := relOf d' x₂ | continue
            -- at least one leg must be derived, or the pair is the same
            -- spelling modulo commutativity (nothing to bridge)
            if s₁ && b' == x₁ && s₂ && d' == x₂ && !comm then continue
            let some e₁ := ← relPf b' x₁ s₁ | continue
            let some e₂ := ← relPf d' x₂ s₂ | continue
            let epPf ← mkEqRefl p
            let eqPf ← if comm then mkAppM ``mul_comm #[y₁, y₂] else mkEqRefl q
            let lem := match s₁, s₂ with
              | true,  true  => ``sr_o4_mul_pp
              | true,  false => ``sr_o4_mul_pn
              | false, true  => ``sr_o4_mul_np
              | false, false => ``sr_o4_mul_nn
            let pf ← mkAppM lem #[e₁, e₂, epPf, eqPf]
            out := out.push (.mkSimple s!"nla_o4_{out.size}", ← inferType pf, pf)
            break
    pure out
  let mut new := false
  for (nm, tyF, pf) in facts do
    new := (← noteFact noted nm tyF pf) || new
  return new

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
    let oc ← runOracle
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
        -- O1 clauses: mined or oracle-derived pivot × sign-unknown cofactor
        let le' (x y : Expr) : MetaM Expr := mkAppM ``LE.le #[x, y]
        let (losA', hisA') := oc.augment a (← mineBounds a)
        let (losB', hisB') := oc.augment b (← mineBounds b)
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
    if tier == 2 then
      -- O4 order-transfer clauses (Z3 generate_mon_ol :163): monomial pairs
      -- with ONE ±-equivalent factor pair — derived, distinct spelling —
      -- and free cofactors. Model-free closure of Z3's sign-selected
      -- clause: both sign cases × both directions. Fully-equivalent pairs
      -- are excluded — the eager bridge already noted their equality.
      let relOf (u v : Expr) : Option Bool :=
        if u == v then some true else oc.pmEquiv u v
      for i in [0:ms.size] do
        for j in [i+1:ms.size] do
          let p := ms[i]!
          let q := ms[j]!
          let some (x₁, x₂) := isIntMul? p | continue
          let some (y₁, y₂) := isIntMul? q | continue
          -- alignments: (shared c from p, d from q, cofactor a, cofactor b,
          -- commuted-p, commuted-q)
          for (c, d, af, bf, commP, commQ) in
              #[(x₂, y₂, x₁, y₁, false, false),
                (x₂, y₁, x₁, y₂, false, true),
                (x₁, y₂, x₂, y₁, true,  false),
                (x₁, y₁, x₂, y₂, true,  true)] do
            if c == d then continue
            let some sgn := oc.pmEquiv d c | continue
            -- cofactors also ±-equivalent ⟹ bridged eagerly, skip
            if (relOf bf af).isSome then continue
            let rhs ← if sgn then pure c else mkAppM ``Neg.neg #[c]
            let some ePf := ← tryDischarge cache (← mkAppM ``Eq #[d, rhs]) | continue
            let epPf ← if commP then mkAppM ``mul_comm #[x₁, x₂] else mkEqRefl p
            let eqPf ← if commQ then mkAppM ``mul_comm #[y₁, y₂] else mkEqRefl q
            let lems := if sgn then
                [``sr_o4_eq_lt, ``sr_o4_eq_gt, ``sr_o4_eq_lt', ``sr_o4_eq_gt']
              else
                [``sr_o4_neg_lt, ``sr_o4_neg_gt, ``sr_o4_neg_lt', ``sr_o4_neg_gt']
            for lem in lems do
              let pf ← mkAppM lem #[ePf, epPf, eqPf]
              out := out.push (.mkSimple s!"nla_cl_{out.size}", ← inferType pf, pf)
    pure out
  for (nm, tyF, pf) in facts do
    let _ ← noteFact noted nm tyF pf

/-- Generation round: div/mod pairs first (their range/quotient facts feed
the monomial sign lattice — the reverse dependency is caught by the next
round), then every monomial, inner monomials first so their facts feed
outer premises; then the pair phase over the completed context. Returns
`true` iff any new fact was noted — the multi-round fixpoint signal. -/
def generate (cache : DCache) (noted : NotedSet) (ms : Array Expr)
    (dps : Array (Expr × Expr)) : TacticM Bool := do
  let mut new := false
  let mut didx := 0
  for (x, y) in dps do
    let facts ← factsForDiv cache x y didx
    let mut notedHere := false
    for (nm, ty, pf) in facts do
      notedHere := (← noteFact noted nm ty pf) || notedHere
    if notedHere then
      cache.modify (·.filter fun _ v => v.isSome)
      new := true
    didx := didx + 1
  let mut idx := 0
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
  let bridgesNew ← generateEquivBridges cache noted ms
  return new || pairsNew || bridgesNew

def saturateCore (stats : Bool := false) (maxRounds : Option Nat := none) : TacticM Unit := do
  let t0 ← IO.monoMsNow
  -- 0. normalize: sum-of-monomials form; doubles as commutative canonization
  evalTactic (← `(tactic| try ring_nf at *))
  if (← getGoals).isEmpty then return
  let t1 ← IO.monoMsNow
  -- 1. collect from hypotheses and goal: monomials, plus div/mod pairs with
  -- symbolic divisors. Each pair's defining-equation product `y * (x / y)`
  -- is appended to the monomial set up front (rounds only re-instantiate
  -- over the initial vocabulary).
  let g ← getMainGoal
  let (ms, dps) ← g.withContext do
    let act : StateRefT (Array Expr) MetaM Unit := do
      for fv in ← g.getNondepPropHyps do
        collectMonomials (← fv.getType)
      collectMonomials (← g.getType)
    let ((), ms) ← act.run #[]
    let actD : StateRefT (Array (Expr × Expr)) MetaM Unit := do
      for fv in ← g.getNondepPropHyps do
        collectDivPairs (← fv.getType)
      collectDivPairs (← g.getType)
    let ((), dps) ← actD.run #[]
    let mut ms := ms
    for (x, y) in dps do
      let d ← mkAppM ``HDiv.hDiv #[x, y]
      let p1 ← mkAppM ``HMul.hMul #[y, d]
      let p2 ← mkAppM ``HMul.hMul #[d, y]
      -- either orientation already collected from the context serves the
      -- product machinery (the defining equation bridges both)
      if !ms.contains p1 && !ms.contains p2 then
        ms := ms.push p1
    pure (ms, dps)
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
  -- round bound: user numeral wins; otherwise depth-adaptive — a
  -- propagation chain crosses one nesting level per round in the worst
  -- (order-reversed) case, so the bound is the deepest monomial nesting
  -- + 1 confirmation round, floored at 3 (the flat-goal default). Postorder
  -- lets one inner-first pass compute depths; div atoms count one level.
  let maxR := maxRounds.getD (Id.run do
    let mut depths : Std.HashMap Expr Nat := {}
    let mut maxDepth := 1
    for m in ms do
      let sub (e : Expr) : Nat := (depths.get? e).getD
        (if (isIntDivMod? e).isSome then 1 else 0)
      let d := match isIntMul? m with
        | some (a, b) => 1 + max (sub a) (sub b)
        | none => match isIntPow? m with
          | some (a, _) => 1 + sub a
          | none => 1
      depths := depths.insert m d
      maxDepth := max maxDepth d
    pure (max 3 (maxDepth + 1)))
  let mut rounds := 0
  for _ in [0:max 1 maxR] do
    let progress ← generate cache noted ms dps
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
      ({ms.size} monomials, {rounds}/{maxR} rounds, {← nlaTacticCall.get} tactic calls, \
      {← nlaCacheHit.get} cache hits, {← nlaLitFast.get} literal fast) \
      · omega {t3 - t2}ms{if retried > 0 then s!" (clause retry tier {retried})" else ""}"

/-- `nla_saturate (n)?` — optional numeral overrides the round bound
(default: depth-adaptive, ≥ 3). -/
elab "nla_saturate" n:(num)? : tactic =>
  saturateCore (maxRounds := n.map (·.getNat))

/-- `nla_saturate` with phase timings and discharge-oracle counters. -/
elab "nla_saturate_stats" n:(num)? : tactic => do
  nlaLitFast.set 0; nlaCacheHit.set 0; nlaTacticCall.set 0
  saturateCore (stats := true) (maxRounds := n.map (·.getNat))

end LeanNonlinearArith.Tactic
