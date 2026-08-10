import LeanNonlinearArith.Nlsat.Trace
import LeanNonlinearArith.Nlsat.TypesOrder
import LeanNonlinearArith.Templates.Quadratic
import Mathlib

/-!
# nla-19a — the checker, semantics layer (TRUSTED)

The meaning of the trace contract's data (`Nlsat/Trace.lean`) over an
arbitrary real valuation `ρ : Nat → ℝ`, split out of `Check.lean` at F5
(R8 of design review 3). No `assume`/`admit`/`external_body`.

This file carries:
1. **Polynomial semantics**: `evalM`/`evalP` — the meaning of `MPoly`
   data — with the homomorphism suite (`evalM_mul`, `evalM_erase`,
   `evalP_add/neg/smulTerm/mul`) and the univariate-form extraction
   (`evalP_coeffsOf`, the linear/quadratic bridges `evalP_linear_form`/
   `evalP_quadratic_form`) that connects payload polys to the explicit
   `a·y + c` / `a·y² + b·y + c` shapes the linearRoot lemmas and the
   S3 kit (`Templates/Quadratic.lean`) consume.
2. **Atom semantics** (`IneqAtom.Holds`, `SHolds`): z3's `ineq_atom`
   sign semantics — `eq` ⟺ some factor vanishes; `lt`/`gt` ⟺ no
   factor vanishes and the odd-factor product has the sign (even
   exponents are sign-absorbed) — plus the multi-factor/even-parity
   collapses (G2/G3, the R-b `List.prod` restatement, and the R-a
   flat `negChain` expansions).
3. **Root-atom semantics**: `rootCmp`, the Thom region formula
   (`thomFormula`), `leadSgn`/`quadRootVal`/`rootVal`, `rootCount`
   with z3's no-roots rule, and `RootAtom.Holds`/`Atom.Holds`/
   `ALitHolds`. The `coeffsOf`↔`coeffsIn` by-value bridge (R3 of
   design review 2).

Canonicity: `evalM_erase` needs `Monomial.Canon`; the checker verifies
canonicity of payload data by `decide` at its boundary.
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

/-! ## Reduction bridges for concrete `MPoly`/`coeffsOf` computation

G4 (census slice): `MPoly.add` is well-founded-compiled, so it does
NOT reduce under kernel whnf/rfl/decide (`MPoly.add [] [(1, [])] =
[(1, [])] := rfl` FAILS) — and every `coeffsOf.go` accumulation step
goes through it; so `coeffsOf` on a concrete polynomial is likewise
not kernel-computable. The per-branch single-step lemmas below restate
the *equation lemmas* for each concrete-merge branch, so a meta
reducer (Refute.lean) can build kernel-checked value equalities
`MPoly.add p q = r` / `coeffsOf p y = cs` on concrete polynomials.
(`MVarId.refl` closers discharge the structural side equalities —
degreeIn/erase/List.set/getElem!/`(c == 0)` — by ordinary whnf; only
`MPoly.add` itself needs this treatment.) -/

namespace MPoly

theorem add_nil_l (q : MPoly) : MPoly.add [] q = q := MPoly.add.eq_1 q

theorem add_nil_r {p : MPoly} (h : p ≠ []) : MPoly.add p [] = p := MPoly.add.eq_2 p h

theorem add_cons_cons_gt {a : Int} {m : Monomial} {p : MPoly}
    {b : Int} {n : Monomial} {q : MPoly}
    (h : Monomial.cmp m n = .gt) :
    MPoly.add ((a, m) :: p) ((b, n) :: q) = (a, m) :: MPoly.add p ((b, n) :: q) := by
  rw [MPoly.add.eq_3, h]

theorem add_cons_cons_lt {a : Int} {m : Monomial} {p : MPoly}
    {b : Int} {n : Monomial} {q : MPoly}
    (h : Monomial.cmp m n = .lt) :
    MPoly.add ((a, m) :: p) ((b, n) :: q) = (b, n) :: MPoly.add ((a, m) :: p) q := by
  rw [MPoly.add.eq_3, h]

theorem add_cons_cons_eq_ne {a : Int} {m : Monomial} {p : MPoly}
    {b : Int} {n : Monomial} {q : MPoly}
    (h : Monomial.cmp m n = .eq) (hz : (a + b == 0) = false) :
    MPoly.add ((a, m) :: p) ((b, n) :: q) = ((a + b), m) :: MPoly.add p q := by
  rw [MPoly.add.eq_3, h]
  simp only [hz, Bool.false_eq_true, reduceIte]

theorem add_cons_cons_eq_zero {a : Int} {m : Monomial} {p : MPoly}
    {b : Int} {n : Monomial} {q : MPoly}
    (h : Monomial.cmp m n = .eq) (hz : (a + b == 0) = true) :
    MPoly.add ((a, m) :: p) ((b, n) :: q) = MPoly.add p q := by
  rw [MPoly.add.eq_3, h]
  simp only [hz, ite_true]

end MPoly

/-- One `coeffsOf.go` cons-step, with all structural redexes replaced by
computed values. (The reducibility analysis above: only the
`MPoly.add` hop needs a proof term; the rest is defeq.) -/
theorem coeffsOf_go_cons (y : Var) (init : List MPoly) (a : Int)
    (m : Monomial) (ts : MPoly) (d : Nat) (v w : MPoly) (init' : List MPoly)
    (hd : Monomial.degreeIn m y = d) (hv : init[d]! = v)
    (hadd : MPoly.add v [(a, Monomial.erase m y)] = w)
    (hset : init.set d w = init') :
    coeffsOf.go y init ((a, m) :: ts) = coeffsOf.go y init' ts := by
  rw [coeffsOf.go.eq_2, hd, hv, hadd, hset]


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
    (hcan : MPoly.Canon p) :
    evalCoeffs ρ y (coeffsOf p y) = evalP ρ p := by
  unfold coeffsOf
  rw [evalCoeffs_go ρ y p _ (fun t ht => (hcan.2 t ht).2) (by
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
    (hdeg : p.degreeIn y = 1) (hcan : MPoly.Canon p) :
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
    (hdeg : p.degreeIn y = 2) (hcan : MPoly.Canon p) :
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

/-! ## Multi-factor / even-parity collapses (G2/G3, design review 7;
R-b restatement, review 9) -/

/-- Positive multi-factor `eq` fact: some factor vanishes ⟹ the product
of the factor VALUES vanishes. Stated as a `List.prod` over
`fs.map Prod.fst` — no `MPoly.mul` in the type, so the fact is
defeq-clean for the zero-product index (R-b; the `factorProd` fold hit
the `MPoly.mul` kernel-reduction trap). -/
theorem holds_multi_eq_prod (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    IneqAtom.Holds ρ ⟨.eq, fs⟩ → ((fs.map Prod.fst).map (evalP ρ)).prod = 0 := by
  intro h
  rcases h with ⟨f, hf, hz⟩
  exact List.prod_eq_zero (List.mem_map.mpr ⟨f.1, List.mem_map.mpr ⟨f, hf, rfl⟩, hz⟩)

/-- The converse direction for the zero-product close (R-b): if no
factor vanishes, the product of values is nonzero. -/
theorem listEvalProd_ne_zero (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    (∀ f ∈ fs.map Prod.fst, evalP ρ f ≠ 0) →
      ((fs.map Prod.fst).map (evalP ρ)).prod ≠ 0 := by
  intro h
  apply List.prod_ne_zero
  intro ha
  obtain ⟨f, hf, hz⟩ := List.mem_map.mp ha
  obtain ⟨g, hg, hgf⟩ := List.mem_map.mp hf
  subst hgf
  exact h g.1 (List.mem_map.mpr ⟨g, hg, rfl⟩) hz

/-- Negative multi-factor `eq` fact (z3's `add_zero_assumption`
composite `∏ pᵢ ≠ 0`): no factor vanishes. Quantified over the
POLYNOMIALS (`fs.map Prod.fst`) so applications have no `Prod.fst`
redex in their type. -/
theorem holds_multi_eq_ne (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    ¬ IneqAtom.Holds ρ ⟨.eq, fs⟩ → ∀ f ∈ fs.map Prod.fst, evalP ρ f ≠ 0 := by
  intro h f hf hz
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
  exact h ⟨g, hg, hz⟩

/-- Positive multi-factor sign facts (even factors are sign-absorbed —
the sign is the odd-factor product's). -/
theorem holds_multi_sign_lt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    IneqAtom.Holds ρ ⟨.lt, fs⟩ → oddProd ρ fs < 0 := (·.2)

theorem holds_multi_sign_gt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    IneqAtom.Holds ρ ⟨.gt, fs⟩ → 0 < oddProd ρ fs := (·.2)

/-- Positive multi-factor sign atoms: no factor vanishes. -/
theorem holds_multi_allNe_lt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    IneqAtom.Holds ρ ⟨.lt, fs⟩ → ∀ f ∈ fs.map Prod.fst, evalP ρ f ≠ 0 :=
  fun h f hf => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact h.1 g hg

theorem holds_multi_allNe_gt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    IneqAtom.Holds ρ ⟨.gt, fs⟩ → ∀ f ∈ fs.map Prod.fst, evalP ρ f ≠ 0 :=
  fun h f hf => by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact h.1 g hg

/-- R-a (review 9): a negative multi-factor sign literal COLLAPSES to
the negated sign when every factor is independently known nonzero
(¬(A ∧ B) with A discharged). Used by `negHolds_chain_*`; the FULL
unconditional form is the `negChain` expansion below. -/
theorem holds_multi_neg_sign_lt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    ¬ IneqAtom.Holds ρ ⟨.lt, fs⟩ → (∀ f ∈ fs.map Prod.fst, evalP ρ f ≠ 0) →
      ¬ oddProd ρ fs < 0 := by
  intro h hne hs
  apply h
  refine ⟨?_, hs⟩
  intro f hf
  exact hne f.1 (List.mem_map.mpr ⟨f, hf, rfl⟩)

theorem holds_multi_neg_sign_gt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    ¬ IneqAtom.Holds ρ ⟨.gt, fs⟩ → (∀ f ∈ fs.map Prod.fst, evalP ρ f ≠ 0) →
      ¬ 0 < oddProd ρ fs := by
  intro h hne hs
  apply h
  refine ⟨?_, hs⟩
  intro f hf
  exact hne f.1 (List.mem_map.mpr ⟨f, hf, rfl⟩)

/-- R-a FULL (review 10): the flat nested-Or expansion of a negative
multi-factor sign atom: `f₁ = 0 ∨ (f₂ = 0 ∨ … ∨ tail)`. NB the
per-factor RECURSIVE form is WRONG — the odd-product sign couples all
odd factors; the correct expansion is flat (some factor vanishes ∨
the whole sign fails). (`g.1`, not a pair pattern, so the cons
equation fires on variables.) -/
def negChain (ρ : Nat → ℝ) : List (MPoly × Bool) → Prop → Prop
  | [], tail => tail
  | g :: rest, tail => evalP ρ g.1 = 0 ∨ negChain ρ rest tail

theorem negChain_tail {ρ : Nat → ℝ} {tail : Prop} :
    ∀ {fs : List (MPoly × Bool)}, tail → negChain ρ fs tail := by
  intro fs h
  induction fs with
  | nil => exact h
  | cons g rest ih => exact Or.inr ih

theorem negChain_mem {ρ : Nat → ℝ} {f : MPoly} {e : Bool} {tail : Prop} :
    evalP ρ f = 0 → ∀ {fs : List (MPoly × Bool)}, (f, e) ∈ fs → negChain ρ fs tail := by
  intro hz fs hm
  induction fs with
  | nil => exact absurd hm (List.not_mem_nil)
  | cons g rest ih =>
    rw [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact Or.inl hz
    · exact Or.inr (ih hm)

/-- The full unconditional expansions: `¬ Holds` for a multi-factor
sign atom is the flat chain `some factor vanishes ∨ the sign fails`. -/
theorem negHolds_chain_lt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    ¬ IneqAtom.Holds ρ ⟨.lt, fs⟩ → negChain ρ fs (¬ oddProd ρ fs < 0) := by
  intro h
  by_cases hall : ∀ g ∈ fs, evalP ρ g.1 ≠ 0
  · exact negChain_tail (holds_multi_neg_sign_lt ρ fs h (fun f hf => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact hall g hg))
  · push_neg at hall
    obtain ⟨⟨g, e⟩, hg, hz⟩ := hall
    exact negChain_mem hz hg

theorem negHolds_chain_gt (ρ : Nat → ℝ) (fs : List (MPoly × Bool)) :
    ¬ IneqAtom.Holds ρ ⟨.gt, fs⟩ → negChain ρ fs (¬ 0 < oddProd ρ fs) := by
  intro h
  by_cases hall : ∀ g ∈ fs, evalP ρ g.1 ≠ 0
  · exact negChain_tail (holds_multi_neg_sign_gt ρ fs h (fun f hf => by
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      exact hall g hg))
  · push_neg at hall
    obtain ⟨⟨g, e⟩, hg, hz⟩ := hall
    exact negChain_mem hz hg

/-! ## Root comparison + Thom region semantics -/

/-- The comparison a root kind asks for: `y ⋈_k r`. -/
def rootCmp (k : RootKind) (Y r : ℝ) : Prop :=
  match k with
  | .eq => Y = r
  | .lt => Y < r
  | .gt => r < Y
  | .le => Y ≤ r
  | .ge => r ≤ Y
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

/-- Resolve `leadSgn` on a positive value (G4 step consumption — the
Thom formula's args must reach lead-free first-order form). -/
theorem leadSgn_of_pos {A : ℝ} (h : 0 < A) : leadSgn A = 1 := by
  unfold leadSgn; rw [if_pos h]

/-- Resolve `leadSgn` on a negative value. -/
theorem leadSgn_of_neg {A : ℝ} (h : A < 0) : leadSgn A = -1 := by
  unfold leadSgn; rw [if_neg (not_lt_of_gt h)]

/-- Root value semantics for quadratics: the i-th root (z3 increasing
order), coefficients sign-normalized to positive lead (flipping `p ↦ −p`
does not change the roots, and for `A < 0` the flip swaps which sqrt
branch is smaller — exactly compensating). -/
noncomputable def quadRootVal (i : Nat) (A B C : ℝ) : ℝ :=
  quadRoot i (leadSgn A * A) (leadSgn A * B) (leadSgn A * C)

/-- Root value of `p` in `y` (deg ≤ 2 fragment, z3 increasing order):
linear ⇒ `-C/A`; quadratic ⇒ sign-normalized `quadRoot` when `A ≠ 0`
at `ρ`, else the degenerate linear root `-C/B` (z3 isolates at the
CURRENT values, `eval_root` :417-437). -/
noncomputable def rootVal (ρ : Nat → ℝ) (y : Var) (i : Nat) (p : MPoly) : ℝ :=
  if p.degreeIn y = 1 then
    -evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!)
  else
    let A := evalP ρ ((coeffsOf p y)[2]!)
    if A ≠ 0 then
      quadRootVal i A (evalP ρ ((coeffsOf p y)[1]!)) (evalP ρ ((coeffsOf p y)[0]!))
    else
      -evalP ρ ((coeffsOf p y)[0]!) / evalP ρ ((coeffsOf p y)[1]!)
/-! ## The coeffsOf↔coeffsIn bridge (R3 of design review 2)

Soundness never needed this (literal matching is by value, mismatch =
sound rejection) — the COVERAGE claim does: the checker's structural
extraction agrees with the solver's `coeffsIn` on every input. -/

theorem forIn_coeffs (l : MPoly) (y : Var) (init : Array MPoly) :
    (forIn l init (fun x r => pure (ForInStep.yield
      (Array.set! r (x.2.degreeIn y) (MPoly.add r[x.2.degreeIn y]! [(x.1, x.2.erase y)])))) :
        Id (Array MPoly)).run =
      l.foldl (fun out (a, m) => Array.set! out (m.degreeIn y)
        (MPoly.add out[m.degreeIn y]! [(a, m.erase y)])) init := by
  induction l generalizing init with
  | nil => simp [forIn]
  | cons t ts ih =>
    obtain ⟨a, m⟩ := t
    rw [List.forIn_cons]
    simp [ih, List.foldl_cons]

theorem coeffsIn_eq_foldl (p : MPoly) (y : Var) :
    p.coeffsIn y = p.foldl (fun out (a, m) => Array.set! out (m.degreeIn y)
        (MPoly.add out[m.degreeIn y]! [(a, m.erase y)]))
        (Array.replicate (p.degreeIn y + 1) []) := by
  unfold MPoly.coeffsIn
  simp only [Id.run]
  show ((forIn p (Array.replicate (p.degreeIn y + 1) []) (fun x r => do
      pure PUnit.unit
      pure (ForInStep.yield (Array.set! r (x.2.degreeIn y)
        (MPoly.add r[x.2.degreeIn y]! [(x.1, x.2.erase y)])))) : Id (Array MPoly)) >>= fun out => pure out).run = _
  simp only [Id.run_bind, Id.run_pure]
  show (forIn p (Array.replicate (p.degreeIn y + 1) []) (fun x r =>
      pure (ForInStep.yield (Array.set! r (x.2.degreeIn y)
        (MPoly.add r[x.2.degreeIn y]! [(x.1, x.2.erase y)])))) : Id (Array MPoly)).run = _
  exact forIn_coeffs p y _

theorem coeffsOf_eq_coeffsIn_toList (p : MPoly) (y : Var) :
    coeffsOf p y = (p.coeffsIn y).toList := by
  rw [coeffsIn_eq_foldl]
  have key : ∀ (l : MPoly) (init : List MPoly),
      coeffsOf.go y init l =
        (l.foldl (fun out (a, m) => Array.set! out (m.degreeIn y)
          (MPoly.add out[m.degreeIn y]! [(a, m.erase y)])) init.toArray).toList := by
    intro l
    induction l with
    | nil => intro init; simp [coeffsOf.go]
    | cons t ts ih =>
      obtain ⟨a, m⟩ := t
      intro init
      rw [List.foldl_cons]
      show coeffsOf.go y (init.set (m.degreeIn y)
          (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])) ts =
        ((ts.foldl (fun out (a, m) => Array.set! out (m.degreeIn y)
          (MPoly.add out[m.degreeIn y]! [(a, m.erase y)]))
          (Array.set! init.toArray (m.degreeIn y)
            (MPoly.add init.toArray[m.degreeIn y]! [(a, m.erase y)]))).toList)
      rw [Array.set!]
      have hset : (init.toArray.setIfInBounds (m.degreeIn y)
          (MPoly.add init.toArray[m.degreeIn y]! [(a, m.erase y)])) =
        (init.set (m.degreeIn y) (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])).toArray := by
        have h2 : (init.set (m.degreeIn y)
            (MPoly.add init[m.degreeIn y]! [(a, m.erase y)])) =
          (init.toArray.setIfInBounds (m.degreeIn y)
            (MPoly.add init.toArray[m.degreeIn y]! [(a, m.erase y)])).toList := by
          have hr : init.toArray.toList = init := rfl
          rw [Array.toList_setIfInBounds, hr, List.getElem!_toArray]
        exact Array.toList_inj.mp h2.symm
      rw [hset]
      exact ih (init.set (m.degreeIn y) (MPoly.add init[m.degreeIn y]! [(a, m.erase y)]))
  unfold coeffsOf
  rw [key p _, List.toArray_replicate]


/-! ## Root-atom semantics with the no-roots rule (R2 of design review 2)

z3's `eval_root` (`nlsat_evaluator.cpp:417-437`): the atom
`y ⋈_k root_i(p)` evaluates FALSE when `i > roots.size()` (the
isolation is at the CURRENT values, so root count is determined by the
degree and the disc/lead signs at `ρ`). This is the semantics the
`rootGeneric` fallback's clause literals get; for deg ≤ 2 it stays
first-order via the same Thom machinery. -/

/-- Root count of `p` as univariate in `y` under `ρ` (deg ≤ 2 fragment):
linear ⇒ 1 if the lc is nonzero else 0; quadratic ⇒ 0/1/2 by the disc
sign when `A ≠ 0`, else the degenerate-linear count (1 if `B ≠ 0`). -/
noncomputable def rootCount (ρ : Nat → ℝ) (y : Var) (p : MPoly) : Nat :=
  if p.degreeIn y = 1 then
    (if evalP ρ ((coeffsOf p y)[1]!) ≠ 0 then 1 else 0)
  else
    let A := evalP ρ ((coeffsOf p y)[2]!)
    let B := evalP ρ ((coeffsOf p y)[1]!)
    let C := evalP ρ ((coeffsOf p y)[0]!)
    if A ≠ 0 then
      (if B^2 - 4*A*C < 0 then 0 else if B^2 - 4*A*C = 0 then 1 else 2)
    else if B ≠ 0 then 1
    else 0

namespace RootAtom

/-- z3 `eval_root` semantics: the atom is FALSE when `i` exceeds the
root count; otherwise the comparison against the i-th root (z3
increasing order). -/
def Holds (ρ : Nat → ℝ) (a : RootAtom) : Prop :=
  a.i ≤ rootCount ρ a.x a.p ∧ rootCmp a.kind (ρ a.x) (rootVal ρ a.x a.i a.p)

end RootAtom

namespace Atom

/-- Full atom semantics: ineq atoms by sign semantics, root atoms by
`RootAtom.Holds` (no-roots rule included). -/
def Holds (ρ : Nat → ℝ) : Atom → Prop
  | .ineq a => IneqAtom.Holds ρ a
  | .root a => RootAtom.Holds ρ a

end Atom

/-- Semantic literal over the full atom type (the F2 extraction's
literal form). -/
def ALitHolds (ρ : Nat → ℝ) (a : Atom) (neg : Bool) : Prop :=
  if neg then ¬ Atom.Holds ρ a else Atom.Holds ρ a

end Check

end LeanNonlinearArith.Nlsat
