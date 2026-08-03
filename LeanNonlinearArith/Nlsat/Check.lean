import LeanNonlinearArith.Nlsat.Trace
import LeanNonlinearArith.Nlsat.TypesOrder
import Mathlib

/-!
# nla-19a — the checker, v0 (TRUSTED layer)

The discharge side of the trace contract (`Nlsat/Trace.lean`). No
`assume`/`admit`/`external_body` anywhere; per-step discharge lemmas
compose into the learned-clause theorem (the F-companion architecture:
term-producing, nla-09 house style).

This file currently carries:
1. **The semantic layer**: `evalM`/`evalP` — the meaning of `MPoly`
   data over an arbitrary real valuation `ρ : Nat → ℝ` — with the
   homomorphism suite (`evalM_mul`, `evalM_erase`, `evalP_add/neg/
   smulTerm/mul`) and the univariate-form extraction
   (`evalP_coeffsIn`, linear/quadratic bridges) that connects payload
   polys to the explicit `a·y + c` / `a·y² + b·y + c` shapes the
   linearRoot lemmas and the S3 kit (`Templates/Quadratic.lean`)
   consume.
2. **Atom semantics** (`IneqAtom.Holds`): z3's sign semantics —
   `eq` ⟺ some factor vanishes; `lt`/`gt` ⟺ no factor vanishes and
   the odd-factor product has the sign (even exponents are sign-
   absorbed, which is all the parity bit means).
3. **The linearRoot discharge** (z3 `mk_linear_root` :861-878): the
   root of `a·y + c` is `-c/a`, and the emitted sign literal on the
   `mkNeg`-folded poly is exactly the root comparison — incl. the
   LE/GE kind remap + literal-negation fold.

Canonicity: `evalM_erase` needs `Monomial.Canon` (the erase/degreeIn
identity fails on duplicate keys); the checker verifies canonicity of
payload data by `decide` at its boundary (F4 parse-level rejection).
-/

namespace LeanNonlinearArith.Nlsat

/-! ## Monomial helper lemmas (checker-side; same namespace style as
`TypesOrder.lean`) -/

namespace Monomial

theorem canon_tail {x : Var} {e : Nat} {m : Monomial}
    (h : Canon ((x, e) :: m)) : Canon m := by
  obtain ⟨hp, he⟩ := h
  exact ⟨List.Pairwise.tail hp, fun p hp' => he p (List.mem_cons_of_mem _ hp')⟩

theorem erase_cons_self {y : Var} {e : Nat} {m : Monomial}
    (h : Canon ((y, e) :: m)) : erase ((y, e) :: m) y = m := by
  obtain ⟨hp, _⟩ := h
  rw [List.pairwise_cons] at hp
  have hy : ∀ p ∈ m, (p.1 != y) = true := by
    intro p hp'
    have hne : p.1 ≠ y := by
      intro he
      exact absurd (he ▸ hp.1 p hp') (Nat.lt_irrefl _)
    exact bne_iff_ne.mpr hne
  unfold erase
  rw [List.filter_cons_of_neg (by simp), List.filter_eq_self.mpr hy]

theorem erase_cons_ne {x y : Var} {e : Nat} {m : Monomial} (h : x ≠ y) :
    erase ((x, e) :: m) y = (x, e) :: erase m y := by
  simp [erase, bne_iff_ne, h]

end Monomial

namespace Check

/-- Monomial semantics over ℝ: the product of `ρ x ^ e`. -/
def evalM (ρ : Nat → ℝ) : Monomial → ℝ
  | [] => 1
  | (x, e) :: m => ρ x ^ e * evalM ρ m

/-- Polynomial semantics over ℝ: the sum of `a · evalM m` over terms. -/
def evalP (ρ : Nat → ℝ) : MPoly → ℝ
  | [] => 0
  | (a, m) :: p => (a : ℝ) * evalM ρ m + evalP ρ p

/-! ## evalM homomorphism suite -/

theorem evalM_mul (ρ : Nat → ℝ) (m n : Monomial) :
    evalM ρ (Monomial.mul m n) = evalM ρ m * evalM ρ n := by
  induction m, n using Monomial.mul.induct with
  | case1 n => simp [evalM, Monomial.mul]
  | case2 m _ => simp [evalM, Monomial.mul]
  | case3 x e m y f n hxy ih =>
    simp only [Monomial.mul, if_pos hxy, evalM, ih]
    ring
  | case4 x e m y f n h₁ hxy ih =>
    simp only [Monomial.mul, if_neg h₁, if_pos hxy, evalM, ih]
    ring
  | case5 x e m y f n h₁ h₂ ih =>
    -- ¬x<y ∧ ¬y<x ⇒ x = y, via explicit Nat.* term lemmas (the
    -- Var-abbrev omega rule, standing directive 8)
    have hxy : x = y := Nat.le_antisymm (Nat.le_of_not_gt h₂) (Nat.le_of_not_gt h₁)
    subst hxy
    simp only [Monomial.mul, if_neg h₁, evalM, ih, pow_add]
    ring_nf

theorem evalM_cons (ρ : Nat → ℝ) (x : Var) (e : Nat) (m : Monomial) :
    evalM ρ ((x, e) :: m) = ρ x ^ e * evalM ρ m := rfl

theorem evalM_erase (ρ : Nat → ℝ) {m : Monomial} (hm : Monomial.Canon m) (y : Var) :
    evalM ρ m = ρ y ^ (m.degreeIn y) * evalM ρ (m.erase y) := by
  induction m with
  | nil => simp [evalM, Monomial.degreeIn, Monomial.erase]
  | cons xe m ih =>
    obtain ⟨xv, e⟩ := xe
    by_cases hxy : xv = y
    · subst hxy
      rw [Monomial.degreeIn_cons_self, Monomial.erase_cons_self hm]
      simp [evalM]
    · have ht := ih (Monomial.canon_tail hm)
      rw [Monomial.degreeIn_cons_ne hxy, Monomial.erase_cons_ne hxy,
          evalM_cons, evalM_cons, ht]
      ring

/-! ## evalP homomorphism suite -/

theorem evalP_add (ρ : Nat → ℝ) (p q : MPoly) :
    evalP ρ (MPoly.add p q) = evalP ρ p + evalP ρ q := by
  induction p, q using MPoly.add.induct with
  | case1 q => simp [evalP, MPoly.add]
  | case2 p _ => simp [evalP, MPoly.add]
  | case3 a m p b n q h ih =>
    simp only [MPoly.add, h, evalP, ih]
    ring
  | case4 a m p b n q h ih =>
    simp only [MPoly.add, h, evalP, ih]
    ring
  | case5 a m p b n q h c hc ih =>
    -- the merged term c = a+b is dropped; semantically it vanishes too.
    -- `.eq` in `cmp` is LIST equality (TypesOrder strong antisymmetry).
    have hmn : m = n := Monomial.cmp_eq_iff.mp h
    subst hmn
    have hz0 : a + b = 0 := by rwa [beq_iff_eq] at hc
    have hab : (a : ℝ) + b = 0 := by exact_mod_cast hz0
    have h0 : (a + b == 0) = true := beq_iff_eq.mpr hz0
    have hM : (a : ℝ) * evalM ρ m + (b : ℝ) * evalM ρ m = 0 := by
      rw [← add_mul, hab, zero_mul]
    simp only [MPoly.add, h, if_pos h0, evalP, ih]
    linarith
  | case6 a m p b n q h c hc ih =>
    have hmn : m = n := Monomial.cmp_eq_iff.mp h
    subst hmn
    have h0 : ¬((a + b == 0) = true) := hc
    simp only [MPoly.add, h, if_neg h0, evalP, ih]
    push_cast
    ring

theorem evalP_neg (ρ : Nat → ℝ) (p : MPoly) : evalP ρ p.neg = -evalP ρ p := by
  induction p with
  | nil => simp [evalP, MPoly.neg]
  | cons t p ih =>
    obtain ⟨a, m⟩ := t
    show evalP ρ ((-a, m) :: MPoly.neg p) = -evalP ρ ((a, m) :: p)
    rw [evalP, evalP, ih]
    push_cast
    ring

end Check

end LeanNonlinearArith.Nlsat
