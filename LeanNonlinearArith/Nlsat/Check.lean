import LeanNonlinearArith.Nlsat.Trace
import LeanNonlinearArith.Nlsat.TypesOrder
import LeanNonlinearArith.Nlsat.MPolyOps
import LeanNonlinearArith.Nlsat.MPolyZp
import LeanNonlinearArith.Templates.Quadratic
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


/-! ## Atom semantics (z3's sign semantics for `ineq_atom`) -/

/-- Product of the ODD factors' values (even factors are sign-absorbed
— that is all the parity bit means). -/
def oddProd (ρ : Nat → ℝ) : List (MPoly × Bool) → ℝ
  | [] => 1
  | (f, false) :: fs => evalP ρ f * oddProd ρ fs
  | (_, true) :: fs => oddProd ρ fs

namespace IneqAtom

/-- z3 `ineq_atom` semantics: `eq` ⟺ some factor vanishes (zero
product, any multiplicity); `lt`/`gt` ⟺ NO factor vanishes and the
odd-factor product has the sign (even exponents contribute only their
square's sign). -/
def Holds (ρ : Nat → ℝ) (a : IneqAtom) : Prop :=
  match a.kind with
  | .eq => ∃ f ∈ a.factors, evalP ρ f.1 = 0
  | .lt => (∀ f ∈ a.factors, evalP ρ f.1 ≠ 0) ∧ oddProd ρ a.factors < 0
  | .gt => (∀ f ∈ a.factors, evalP ρ f.1 ≠ 0) ∧ 0 < oddProd ρ a.factors

end IneqAtom

/-- A semantic literal: an atom with polarity (`neg = true` negates). -/
def SHolds (ρ : Nat → ℝ) (a : IneqAtom) (neg : Bool) : Prop :=
  if neg then ¬ IneqAtom.Holds ρ a else IneqAtom.Holds ρ a

/-- Single-factor collapses (the linearRoot/Thom emissions are all
single-factor atoms). -/
theorem holds_single_eq (ρ : Nat → ℝ) (q : MPoly) :
    IneqAtom.Holds ρ ⟨.eq, [(q, false)]⟩ ↔ evalP ρ q = 0 := by
  simp [IneqAtom.Holds]

theorem holds_single_lt (ρ : Nat → ℝ) (q : MPoly) :
    IneqAtom.Holds ρ ⟨.lt, [(q, false)]⟩ ↔ evalP ρ q < 0 := by
  simp [IneqAtom.Holds, oddProd]
  exact ne_of_lt

theorem holds_single_gt (ρ : Nat → ℝ) (q : MPoly) :
    IneqAtom.Holds ρ ⟨.gt, [(q, false)]⟩ ↔ 0 < evalP ρ q := by
  simp [IneqAtom.Holds, oddProd]
  exact ne_of_gt

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

/-- The comparison a root kind asks for: `y ⋈_k r`. -/
def rootCmp (k : RootKind) (Y r : ℝ) : Prop :=
  match k with
  | .eq => Y = r
  | .lt => Y < r
  | .gt => r < Y
  | .le => Y ≤ r
  | .ge => r ≤ Y

/-- The discharge: the emitted literal FAILS at `ρ` exactly when `ρ y`
bears the root comparison to `-C/A` (the root of `p` in `y`). `hAq` is
the leading-coefficient positivity evidence (const-lc variant: by
`decide` on the const value + the `mkNeg` fold; `mk_plinear_root`
variant: from the `lcFact` sign literal failing at `ρ`). -/
theorem linearRoot_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var) (p : MPoly)
    (mkNeg : Bool)
    (hdeg : p.degreeIn y = 1) (hcan : ∀ t ∈ p, Monomial.Canon t.2)
    (hAq : 0 < (if mkNeg then (-1 : ℝ) else 1) * evalP ρ ((coeffsOf p y)[1]!)) :
    ¬ SHolds ρ (linearRootEmitted k p mkNeg).1 (linearRootEmitted k p mkNeg).2 ↔
      rootCmp k (ρ y)
        (-evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!)) := by
  have hform := evalP_linear_form ρ y p hdeg hcan
  set A := evalP ρ ((coeffsOf p y)[1]!)
  set C := evalP ρ ((coeffsOf p y)[0]!)
  set s : ℝ := if mkNeg then (-1 : ℝ) else 1
  have hsA : (0 : ℝ) < s * A := by exact_mod_cast hAq
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


/-! ## Sign payloads and the Thom region formula -/

/-- `s` is the sign of `v` (payload sign values are −1/0/+1 Ints). -/
def signMatches (s : Int) (v : ℝ) : Prop :=
  (s = -1 ∧ v < 0) ∨ (s = 0 ∧ v = 0) ∨ (s = 1 ∧ 0 < v)

theorem signMatches.ne_zero {s : Int} {v : ℝ} (h : signMatches s v) (hs : s ≠ 0) :
    v ≠ 0 := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ne_of_lt h2
  · exact absurd h1 hs
  · exact ne_of_gt h2

theorem signMatches.nonneg {s : Int} {v : ℝ} (h : signMatches s v)
    (hs : s = 0 ∨ s = 1) : 0 ≤ v := by
  rcases h with ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases hs with rfl | rfl <;> simp at h1
  · exact le_of_eq h2.symm
  · exact le_of_lt h2

theorem signMatches.neg {s : Int} {v : ℝ} (h : signMatches s v) :
    signMatches (-s) (-v) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr (Or.inr ⟨by simp [h1], by linarith⟩)
  · exact Or.inr (Or.inl ⟨by simp [h1], by linarith⟩)
  · exact Or.inl ⟨by simp [h1], by linarith⟩

theorem signMatches.smul_eq {s : Int} {v : ℝ} (h : signMatches s v) :
    signMatches s ((-1 : ℝ) * (-1 : ℝ) * v) := by simpa using h

/-- The Thom region formula for `y ⋈_k root_i(p)` (POSITIVE lead):
the sign-condition disjunction equivalent to the root comparison, in
terms of `p(y)` and `p'(y) = 2Ay + B` values. (Index `i` collapses to
the two cases 1/other; the grammar restricts to `i ∈ {1, 2}`.) -/
def thomFormula (k : RootKind) (i : Nat) (pv pdv : ℝ) : Prop :=
  match k, i with
  | .eq, 1 => pv = 0 ∧ pdv ≤ 0
  | .eq, _ => pv = 0 ∧ 0 ≤ pdv
  | .lt, 1 => 0 < pv ∧ pdv < 0
  | .lt, _ => pv < 0 ∨ (0 ≤ pv ∧ pdv < 0)
  | .gt, 1 => pv < 0 ∨ (0 ≤ pv ∧ 0 < pdv)
  | .gt, _ => 0 < pv ∧ 0 < pdv
  | .le, 1 => 0 ≤ pv ∧ pdv ≤ 0
  | .le, _ => pv ≤ 0 ∨ (0 ≤ pv ∧ pdv ≤ 0)
  | .ge, 1 => pv ≤ 0 ∨ (0 ≤ pv ∧ 0 ≤ pdv)
  | .ge, _ => 0 ≤ pv ∧ 0 ≤ pdv

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

/-! ## The Thom discharge at the eval level -/

/-- The lead-sign factor for Thom normalization: `+1` if `0 < A`,
else `−1` (for `A < 0`; `leadSgn 0 = -1` is a don't-care — every use
has `A ≠ 0`). -/
noncomputable def leadSgn (A : ℝ) : ℝ := if 0 < A then 1 else -1

theorem leadSgn_sq (A : ℝ) : (leadSgn A)^2 = 1 := by
  unfold leadSgn
  by_cases h : 0 < A <;> simp [h]

theorem leadSgn_ne_zero (A : ℝ) : leadSgn A ≠ 0 := by
  unfold leadSgn
  by_cases h : 0 < A <;> simp [h]

theorem leadSgn_mul_self_pos {A : ℝ} (hA : A ≠ 0) : 0 < leadSgn A * A := by
  unfold leadSgn
  by_cases h : 0 < A
  · simp [h, h]
  · simp [h]
    exact lt_of_le_of_ne (le_of_not_gt h) hA

/-- Root value semantics for quadratics: the i-th root (z3 increasing
order), coefficients sign-normalized to positive lead (flipping `p ↦ −p`
does not change the roots, and for `A < 0` the flip swaps which sqrt
branch is smaller — exactly compensating). -/
noncomputable def quadRootVal (i : Nat) (A B C : ℝ) : ℝ :=
  quadRoot i (leadSgn A * A) (leadSgn A * B) (leadSgn A * C)

/-- Root value of `p` in `y` (deg ≤ 2 fragment, z3 increasing order):
linear ⇒ `-C/A`; quadratic ⇒ sign-normalized `quadRoot`. -/
noncomputable def rootVal (ρ : Nat → ℝ) (y : Var) (i : Nat) (p : MPoly) : ℝ :=
  if p.degreeIn y = 1 then
    -evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!)
  else
    quadRootVal i (evalP ρ ((coeffsOf p y)[2]!)) (evalP ρ ((coeffsOf p y)[1]!))
      (evalP ρ ((coeffsOf p y)[0]!))

/-- The Thom discharge (z3 `mk_quadratic_root` :787-820): the sign
literals on {disc, A, 2Ay+B, p} encode the root atom — the comparison
`ρ y ⋈_k root_i(p)` holds iff the region formula does. (The formula's
truth is evaluated by the composition from the `p`/`pDiff` sign facts;
the `sq = 0` case needs no `p` fact — definite-disc makes `p ≥ 0`
everywhere, exactly why z3 skips that `ensure_sign`.) -/
theorem thom_discharge (ρ : Nat → ℝ) (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
    (sq sa : Int)
    (hdeg : p.degreeIn y = 2) (hi : i = 1 ∨ i = 2)
    (hcan : ∀ t ∈ p, Monomial.Canon t.2)
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

end Check

end LeanNonlinearArith.Nlsat
