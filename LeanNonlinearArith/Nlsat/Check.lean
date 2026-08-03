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

/-! ## evalP homomorphism suite (continued): smulTerm, mul, atoms -/

theorem evalP_smulTerm (ρ : Nat → ℝ) (c : Int) (mo : Monomial) (p : MPoly) :
    evalP ρ (MPoly.smulTerm c mo p) = (c : ℝ) * evalM ρ mo * evalP ρ p := by
  by_cases hc : c == 0
  · have hz : c = 0 := beq_iff_eq.mp hc
    simp [MPoly.smulTerm, hc, hz, evalP]
  · have hcz : c ≠ 0 := by
      intro h; exact hc (by simp [h])
    induction p with
    | nil => simp [MPoly.smulTerm, hcz, evalP]
    | cons t p ih =>
      obtain ⟨a, m⟩ := t
      have hstep : MPoly.smulTerm c mo ((a, m) :: p) =
          (c * a, Monomial.mul mo m) :: MPoly.smulTerm c mo p := by
        simp [MPoly.smulTerm, hcz]
      rw [hstep, evalP, ih, evalP, evalM_mul]
      push_cast
      ring

theorem evalP_mul (ρ : Nat → ℝ) (p q : MPoly) :
    evalP ρ (MPoly.mul p q) = evalP ρ p * evalP ρ q := by
  have key : ∀ (ts : MPoly) (acc : MPoly),
      evalP ρ (ts.foldl (fun acc t => MPoly.add acc (MPoly.smulTerm t.1 t.2 q)) acc) =
        evalP ρ acc + evalP ρ ts * evalP ρ q := by
    intro ts
    induction ts with
    | nil => intro acc; simp [evalP]
    | cons t ts ih =>
      obtain ⟨a, m⟩ := t
      intro acc
      rw [List.foldl_cons, ih, evalP_add, evalP_smulTerm]
      simp only [evalP]
      ring
  rw [MPoly.mul, key p []]
  simp [evalP]

theorem evalP_ofInt (ρ : Nat → ℝ) (n : Int) : evalP ρ (MPoly.ofInt n) = n := by
  by_cases h : n == 0
  · have hz : n = 0 := beq_iff_eq.mp h
    simp [MPoly.ofInt, h, hz, evalP]
  · have hz : n ≠ 0 := by intro h'; exact h (by simp [h'])
    simp [MPoly.ofInt, hz, evalP, evalM]

theorem evalP_ofVar (ρ : Nat → ℝ) (x : Var) : evalP ρ (MPoly.ofVar x) = ρ x := by
  simp [MPoly.ofVar, evalP, evalM]

/-! ## Checker-side coefficient extraction + univariate forms

`coeffsOf` is a structural mirror of `MPoly.coeffsIn` (list-based; no
for-in plumbing). The checker uses it for ALL A/B/C extraction and
matches reconstructed polys against emitted literals BY VALUE — so no
bridge theorem to the solver's `coeffsIn` is needed (a mismatch is a
parse-level rejection, the sound failure mode — F4). -/

/-- Horner-form evaluation of a coefficient list as a polynomial in `y`:
`evalCoeffs [c₀, c₁, …, c_d] = c₀ + ρy·(c₁ + ρy·(…))`. -/
def evalCoeffs (ρ : Nat → ℝ) (y : Var) : List MPoly → ℝ
  | [] => 0
  | c :: cs => evalP ρ c + ρ y * evalCoeffs ρ y cs

/-- Structural coefficient extraction: `coeffsOf p y` is the coefficient
list of `p` viewed as univariate in `y` (index = degree in `y`). -/
def coeffsOf (p : MPoly) (y : Var) : List MPoly :=
  go (List.replicate (p.degreeIn y + 1) []) p
where
  go (init : List MPoly) : MPoly → List MPoly
    | [] => init
    | (a, m) :: ts =>
      go (init.set (m.degreeIn y) (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])) ts

theorem evalCoeffs_set (ρ : Nat → ℝ) (y : Var) (cs : List MPoly) (e : Nat)
    (v : MPoly) (he : e < cs.length) :
    evalCoeffs ρ y (cs.set e v) =
      evalCoeffs ρ y cs + (evalP ρ v - evalP ρ cs[e]!) * ρ y ^ e := by
  induction e generalizing cs with
  | zero =>
    match cs, he with
    | c :: cs', _ =>
      have hget : (c :: cs')[0]! = c := by simp
      simp only [List.set, evalCoeffs, hget]
      ring
  | succ e ih =>
    match cs, he with
    | c :: cs', h =>
      simp only [List.set, evalCoeffs]
      have hlen : e < cs'.length := by
        have hh : (c :: cs').length = cs'.length + 1 := rfl
        omega
      rw [ih cs' hlen]
      have hget : (c :: cs')[e + 1]! = cs'[e]! := by simp
      rw [hget, pow_succ]
      ring

theorem evalCoeffs_go (ρ : Nat → ℝ) (y : Var) (ts : MPoly) (init : List MPoly)
    (hcan : ∀ t ∈ ts, Monomial.Canon t.2)
    (hdeg : ∀ t ∈ ts, t.2.degreeIn y < init.length) :
    evalCoeffs ρ y (coeffsOf.go y init ts) = evalCoeffs ρ y init + evalP ρ ts := by
  induction ts generalizing init with
  | nil => simp [coeffsOf.go, evalP]
  | cons t ts ih =>
    obtain ⟨a, m⟩ := t
    have hc : Monomial.Canon m := hcan (a, m) List.mem_cons_self
    have hd : m.degreeIn y < init.length := hdeg (a, m) List.mem_cons_self
    have hcan' : ∀ t ∈ ts, Monomial.Canon t.2 :=
      fun t ht => hcan t (List.mem_cons_of_mem _ ht)
    have hdeg' : ∀ t ∈ ts, t.2.degreeIn y < (init.set (m.degreeIn y)
        (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])).length :=
      fun t ht => by
        rw [List.length_set]
        exact hdeg t (List.mem_cons_of_mem _ ht)
    show evalCoeffs ρ y
        (coeffsOf.go y (init.set (m.degreeIn y)
          (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])) ts) =
      evalCoeffs ρ y init + evalP ρ ((a, m) :: ts)
    rw [ih _ hcan' hdeg']
    have hstep : evalCoeffs ρ y (init.set (m.degreeIn y)
        (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])) =
        evalCoeffs ρ y init + (a : ℝ) * evalM ρ m := by
      rw [evalCoeffs_set ρ y init (m.degreeIn y) _ hd, evalP_add]
      have hsn : evalP ρ [(a, m.erase y)] = (a : ℝ) * evalM ρ (m.erase y) := by
        simp [evalP]
      rw [hsn]
      have her := evalM_erase ρ hc y
      rw [her]
      ring
    rw [hstep]
    simp only [evalP]
    ring

theorem evalCoeffs_replicate (ρ : Nat → ℝ) (y : Var) (n : Nat) :
    evalCoeffs ρ y (List.replicate n []) = 0 := by
  induction n with
  | zero => simp [evalCoeffs]
  | succ n ih => simp [List.replicate, evalCoeffs, evalP, ih]

theorem MPoly.degreeIn_le_of_mem (y : Var) {p : MPoly} :
    ∀ t ∈ p, t.2.degreeIn y ≤ p.degreeIn y := by
  have key : ∀ (l : MPoly) (acc : Nat),
      (∀ t ∈ l, t.2.degreeIn y ≤
          l.foldl (fun acc (_, m) => max acc (m.degreeIn y)) acc) ∧
      acc ≤ l.foldl (fun acc (_, m) => max acc (m.degreeIn y)) acc := by
    intro l
    induction l with
    | nil => intro acc; constructor <;> simp
    | cons t l ih =>
      intro acc
      obtain ⟨a, m⟩ := t
      rw [List.foldl_cons]
      have ihr := (ih (max acc (m.degreeIn y))).2
      have ihl := (ih (max acc (m.degreeIn y))).1
      constructor
      · intro t' ht'
        cases List.mem_cons.mp ht' with
        | inl heq =>
          subst heq
          exact Nat.le_trans (Nat.le_max_right _ _) ihr
        | inr hmem =>
          exact ihl t' hmem
      · exact Nat.le_trans (Nat.le_max_left _ _) ihr
  intro t ht
  exact (key p 0).1 t ht

theorem evalP_coeffsOf (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hcan : ∀ t ∈ p, Monomial.Canon t.2) :
    evalCoeffs ρ y (coeffsOf p y) = evalP ρ p := by
  unfold coeffsOf
  rw [evalCoeffs_go ρ y p _ hcan (by
    intro t ht
    rw [List.length_replicate]
    exact Nat.lt_succ_of_le (MPoly.degreeIn_le_of_mem y t ht)),
    evalCoeffs_replicate, zero_add]

theorem coeffsOf_length (p : MPoly) (y : Var) :
    (coeffsOf p y).length = p.degreeIn y + 1 := by
  unfold coeffsOf
  have : ∀ (ts : MPoly) (init : List MPoly),
      (coeffsOf.go y init ts).length = init.length := by
    intro ts
    induction ts with
    | nil => intro init; rfl
    | cons t ts ih =>
      intro init
      show (coeffsOf.go y (init.set (t.2.degreeIn y) _) ts).length = init.length
      rw [ih, List.length_set]
  rw [this, List.length_replicate]

/-- The linear-form bridge: `p` of degree 1 in `y` evaluates as
`A·ρy + C` with `A = coeffsOf[1]`, `C = coeffsOf[0]`. -/
theorem evalP_linear_form (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 1) (hcan : ∀ t ∈ p, Monomial.Canon t.2) :
    evalP ρ p =
      evalP ρ ((coeffsOf p y)[1]!) * ρ y + evalP ρ ((coeffsOf p y)[0]!) := by
  rw [← evalP_coeffsOf ρ y p hcan]
  have hlen : (coeffsOf p y).length = 2 := by rw [coeffsOf_length, hdeg]
  obtain ⟨c0, c1, h⟩ := List.length_eq_two.mp hlen
  have g0 : (([c0, c1] : List MPoly))[0]! = c0 := by simp
  have g1 : (([c0, c1] : List MPoly))[1]! = c1 := by simp
  rw [h, g0, g1]
  simp [evalCoeffs]
  ring

/-- The quadratic-form bridge: `p` of degree 2 in `y` evaluates as
`A·ρy² + B·ρy + C`. -/
theorem evalP_quadratic_form (ρ : Nat → ℝ) (y : Var) (p : MPoly)
    (hdeg : p.degreeIn y = 2) (hcan : ∀ t ∈ p, Monomial.Canon t.2) :
    evalP ρ p =
      evalP ρ ((coeffsOf p y)[2]!) * (ρ y)^2 +
        evalP ρ ((coeffsOf p y)[1]!) * ρ y + evalP ρ ((coeffsOf p y)[0]!) := by
  rw [← evalP_coeffsOf ρ y p hcan]
  have hlen : (coeffsOf p y).length = 3 := by rw [coeffsOf_length, hdeg]
  obtain ⟨c0, c1, c2, h⟩ := List.length_eq_three.mp hlen
  have g0 : (([c0, c1, c2] : List MPoly))[0]! = c0 := by simp
  have g1 : (([c0, c1, c2] : List MPoly))[1]! = c1 := by simp
  have g2 : (([c0, c1, c2] : List MPoly))[2]! = c2 := by simp
  rw [h, g0, g1, g2]
  simp [evalCoeffs]
  ring

end Check

end LeanNonlinearArith.Nlsat
