import Mathlib

/-!
# Census specimen corpus — verus-rational (nla-03)

Failing sites from the 2026-07-24 census (verus-rational verified with
`smt.arith.nl.nra=false`: 692 verified / 39 errors), transcribed as Lean goals
with exactly the hypotheses the Verus `by (nonlinear_arith) requires` clauses
pass (these queries are context-free in Verus). Verus `int` ↦ `ℤ`.

Purpose: baseline what existing Lean automation closes before building L1.
Findings so far are recorded per specimen. Naming: `<file>_<line>`.

Push-button probe results (2026-07-24, lean/mathlib v4.25.0):
* `division_699`: closes with bare `grind` (its Gröbner module) — no hints.
* `cauchy_schwarz_233`: `subst; ring`, trivially.
* `ordering_139`: closes with bare `nlinarith` — no hints; `grind` fails on it
  (cutsat + ring have no product-of-hypotheses search). The hinted forms below
  are kept as the deterministic versions the L1 layer would emit.
-/

namespace LeanNonlinearArith.Corpus

/-- division.rs:699 — equivalence of products after factoring an inverse.
Pure ideal membership. Baseline: closes with subst + `linear_combination`
(one explicit multiplier); the L1 Gröbner layer should get this push-button. -/
theorem division_699 (a_num b_num ic_num lhs_num rhs_num : ℤ)
    (a_den b_den ic_den lhs_den rhs_den : ℤ)
    (h1 : a_num * (b_den + 1) = b_num * (a_den + 1))
    (h2 : lhs_num = a_num * ic_num)
    (h3 : rhs_num = b_num * ic_num)
    (h4 : lhs_den + 1 = (a_den + 1) * (ic_den + 1))
    (h5 : rhs_den + 1 = (b_den + 1) * (ic_den + 1)) :
    lhs_num * (rhs_den + 1) = rhs_num * (lhs_den + 1) := by
  subst h2 h3
  rw [h4, h5]
  linear_combination (ic_num * (ic_den + 1)) * h1

/-- cauchy_schwarz.rs:233 — a product regrouping. Baseline: `subst` + `ring`. -/
theorem cauchy_schwarz_233 (xn dy dz t1 v1 : ℤ)
    (ht : t1 = ((xn * xn) * (dy * dy)) * (dz * dz))
    (hv : v1 = xn * dy * dz) :
    t1 = v1 * v1 := by
  subst ht hv; ring

/-- ordering.rs:139 — transitivity of `≤` on fractions: the one genuinely
order-theoretic specimen of the three. Baseline: `nlinarith` needs product
hints (the two cross-multiplications); plain `nlinarith` also worth testing. -/
theorem ordering_139 (a_num b_num c_num da db dc : ℤ)
    (hab : a_num * db ≤ b_num * da)
    (hbc : b_num * dc ≤ c_num * db)
    (hda : 0 < da) (hdb : 0 < db) (hdc : 0 < dc) :
    a_num * dc ≤ c_num * da := by
  nlinarith [mul_le_mul_of_nonneg_right hab hdc.le,
             mul_le_mul_of_nonneg_right hbc hda.le,
             mul_pos hdb (mul_pos hda hdc)]

end LeanNonlinearArith.Corpus
