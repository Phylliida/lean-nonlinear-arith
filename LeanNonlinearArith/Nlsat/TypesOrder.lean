import Mathlib
import LeanNonlinearArith.Nlsat.Types

/-!
# nla-25.4 — order theorems for `Monomial.cmp` + canonical-form preservation

Proof layer over `Nlsat/Types.lean` — no ported code is touched; every
theorem here is about the definitions exactly as they ship.

Contents:

* **Order properties of `Monomial.cmp`** (= z3 `lex_compare`,
  `polynomial.cpp:625`): `cmp_refl`, `cmp_eq_iff` (antisymmetry in the
  strong form — `.eq` forces *list equality*, with no canonicity
  hypothesis, because `go` demands positional agreement), `cmp_swap`
  (totality/asymmetry), `cmp_lt_trans`/`cmp_gt_trans`.

* **Canonical-form predicates** `Monomial.Canon` (strictly increasing
  variable indices, positive exponents) and `MPoly.Canon` (nonzero
  coefficients, monomials strictly descending in `cmp`, each canonical)
  — the invariants stated informally in Types.lean docstrings — and
  preservation through `Monomial.mul` and
  `MPoly.add`/`neg`/`sub`/`smulTerm`/`mul`.

* **The keystone** for `MPoly.mul` (whose `smulTerm` maps the monomials
  of a canonical polynomial through `Monomial.mul mo ·`):
  `Monomial.cmp_mul_left` — multiplying by a fixed canonical monomial
  is an order-*equality*, `cmp (mul k m) (mul k n) = cmp m n`. Proved
  via a dense exponent-vector characterization (`denseCompare`:
  compare `degreeIn` from the top variable down), which is
  representation-order-free; `degreeIn_mul` (exponents add under the
  sorted merge) and translation-invariance of `Nat.compare` finish it.
  Fidelity note on who owes this theorem: **z3 does not rely on it** —
  z3 products are accumulated unsorted (`som_buffer`) and `m_lex_sorted`
  is only ever set by an explicit `lex_sort` (bucket sort, never carried
  through a product). The obligation is created by *our* eager
  representation, whose `smulTerm` keeps sorted storage without
  re-sorting; z3 pays a re-sort where we pay this theorem.

Proof-engineering note: `omega` in this toolchain only recognizes
comparisons whose head type argument is literally `Nat`/`Int` — facts
headed by the (reducible!) `Var` abbrev are invisible to it. Hence the
helper lemmas below carry `Nat` binders (their instantiations produce
`Nat`-headed facts), and reasoning about key comparisons uses explicit
`Nat.*` term lemmas instead of `omega`.
-/

namespace LeanNonlinearArith.Nlsat

namespace Monomial

/-! ### Order properties of `lexCompare.go` (raw list level) -/

theorem go_refl (a : Monomial) : lexCompare.go a a = .eq := by
  induction a with
  | nil => rfl
  | cons p t ih => obtain ⟨x, e⟩ := p; simp [lexCompare.go, ih]

/-- `.eq` forces positional equality — no canonicity needed. -/
theorem go_eq_iff {a b : Monomial} : lexCompare.go a b = .eq ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [lexCompare.go]
  | cons p m ih =>
    obtain ⟨x, e⟩ := p
    cases b with
    | nil => simp [lexCompare.go]
    | cons q n =>
      obtain ⟨y, f⟩ := q
      rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
      · simp [lexCompare.go, gt_iff_lt, Nat.ne_of_lt hxy, Nat.lt_asymm hxy]
      · subst hxy
        by_cases hef : e = f
        · subst hef; simp [lexCompare.go, ih]
        · rcases Nat.lt_trichotomy e f with h | h | h
          · simp [lexCompare.go, hef, h]
          · exact absurd h hef
          · simp [lexCompare.go, hef, Nat.lt_asymm h]
      · simp [lexCompare.go, gt_iff_lt, (Nat.ne_of_lt hxy).symm, hxy]

theorem go_swap (a b : Monomial) : lexCompare.go a b = (lexCompare.go b a).swap := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons p m ih =>
    obtain ⟨x, e⟩ := p
    cases b with
    | nil => rfl
    | cons q n =>
      obtain ⟨y, f⟩ := q
      rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
      · simp [lexCompare.go, gt_iff_lt, Nat.ne_of_lt hxy, (Nat.ne_of_lt hxy).symm,
              Nat.lt_asymm hxy, hxy, Ordering.swap]
      · subst hxy
        by_cases hef : e = f
        · subst hef; simp [lexCompare.go, ih]
        · rcases Nat.lt_trichotomy e f with h | h | h
          · simp [lexCompare.go, hef, Ne.symm hef, h, Nat.lt_asymm h, Ordering.swap]
          · exact absurd h hef
          · simp [lexCompare.go, hef, Ne.symm hef, h, Nat.lt_asymm h, Ordering.swap]
      · simp [lexCompare.go, gt_iff_lt, Nat.ne_of_lt hxy, (Nat.ne_of_lt hxy).symm,
              Nat.lt_asymm hxy, hxy, Ordering.swap]

/-- Head-level characterization of `.lt` for the cons/cons case.
`Nat` binders on purpose: rewriting with this produces `Nat`-headed
comparison facts that `omega` can consume. -/
theorem go_cons_cons_lt {x y e f : Nat} {m n : Monomial} :
    lexCompare.go ((x, e) :: m) ((y, f) :: n) = .lt ↔
      x < y ∨ (x = y ∧ e < f) ∨ (x = y ∧ e = f ∧ lexCompare.go m n = .lt) := by
  rcases Nat.lt_trichotomy x y with hxy | hxy | hxy
  · simp [lexCompare.go, gt_iff_lt, Nat.ne_of_lt hxy, Nat.lt_asymm hxy, hxy]
  · subst hxy
    by_cases hef : e = f
    · subst hef; simp [lexCompare.go]
    · rcases Nat.lt_trichotomy e f with h | h | h
      · simp [lexCompare.go, hef, h]
      · exact absurd h hef
      · simp [lexCompare.go, hef, Nat.lt_asymm h]
  · simp [lexCompare.go, gt_iff_lt, (Nat.ne_of_lt hxy).symm, Nat.lt_asymm hxy, hxy]

theorem go_lt_trans {a : Monomial} : ∀ {b c : Monomial},
    lexCompare.go a b = .lt → lexCompare.go b c = .lt → lexCompare.go a c = .lt := by
  induction a with
  | nil =>
    intro b c h₁ h₂
    cases b with
    | nil => exact absurd h₁ (by simp [lexCompare.go])
    | cons q n =>
      cases c with
      | nil => exact absurd h₂ (by simp [lexCompare.go])
      | cons r k => rfl
  | cons p m ih =>
    obtain ⟨x, e⟩ := p
    intro b c h₁ h₂
    cases b with
    | nil => exact absurd h₁ (by simp [lexCompare.go])
    | cons q n =>
      obtain ⟨y, f⟩ := q
      cases c with
      | nil => exact absurd h₂ (by simp [lexCompare.go])
      | cons r k =>
        obtain ⟨z, g⟩ := r
        rw [go_cons_cons_lt] at h₁ h₂ ⊢
        rcases h₁ with h | ⟨hxy, h⟩ | ⟨hxy, hef, h⟩ <;>
          rcases h₂ with h' | ⟨hyz, h'⟩ | ⟨hyz, hfg, h'⟩ <;>
          first
            | exact .inl (by omega)
            | exact .inr (.inl ⟨by omega, by omega⟩)
            | exact .inr (.inr ⟨by omega, by omega, ih h h'⟩)

/-- A cons whose head variable dominates every key of `a` beats it — the
one-step semantic content of "biggest variable dominates". -/
theorem go_lt_of_keys_lt {a : Monomial} {y : Nat} {f : Nat} {n : Monomial}
    (h : ∀ p ∈ a, p.1 < y) : lexCompare.go a ((y, f) :: n) = .lt := by
  cases a with
  | nil => rfl
  | cons p t =>
    obtain ⟨x, e⟩ := p
    have hx : x < y := h (x, e) (by simp)
    simp [lexCompare.go, gt_iff_lt, Nat.ne_of_lt hx, Nat.lt_asymm hx]

theorem go_gt_of_keys_lt {a : Monomial} {y : Nat} {f : Nat} {n : Monomial}
    (h : ∀ p ∈ a, p.1 < y) : lexCompare.go ((y, f) :: n) a = .gt := by
  cases a with
  | nil => rfl
  | cons p t =>
    obtain ⟨x, e⟩ := p
    have hx : x < y := h (x, e) (by simp)
    simp [lexCompare.go, gt_iff_lt, (Nat.ne_of_lt hx).symm, hx]

/-! ### Order properties of `cmp` (lifted through the reversal) -/

theorem cmp_refl (m : Monomial) : cmp m m = .eq := go_refl m.reverse

/-- Antisymmetry, strong form: `.eq` is *list equality* (`go` demands
positional agreement, and `reverse` is injective). -/
theorem cmp_eq_iff {m n : Monomial} : cmp m n = .eq ↔ m = n := by
  unfold cmp lexCompare
  rw [go_eq_iff, List.reverse_inj]

/-- Totality/asymmetry: swapping arguments swaps the verdict. -/
theorem cmp_swap (m n : Monomial) : cmp m n = (cmp n m).swap :=
  go_swap m.reverse n.reverse

theorem cmp_lt_trans {a b c : Monomial} (h₁ : cmp a b = .lt) (h₂ : cmp b c = .lt) :
    cmp a c = .lt := go_lt_trans h₁ h₂

theorem cmp_gt_trans {a b c : Monomial} (h₁ : cmp a b = .gt) (h₂ : cmp b c = .gt) :
    cmp a c = .gt := by
  have h₁' : cmp b a = .lt := by rw [cmp_swap, h₁]; rfl
  have h₂' : cmp c b = .lt := by rw [cmp_swap, h₂]; rfl
  have h := cmp_lt_trans h₂' h₁'
  rw [cmp_swap, h]; rfl

/-! ### Canonical monomials -/

/-- Canonical monomial: strictly increasing variable indices, positive
exponents (the representation invariant from the Types.lean docstring). -/
def Canon (m : Monomial) : Prop :=
  m.Pairwise (fun p q => p.1 < q.1) ∧ ∀ p ∈ m, 0 < p.2

theorem canon_nil : Canon [] := ⟨List.Pairwise.nil, by simp⟩

theorem degreeIn_nil {x : Var} : degreeIn [] x = 0 := rfl

theorem degreeIn_cons_self {x : Var} {e : Nat} {t : Monomial} :
    degreeIn ((x, e) :: t) x = e := by
  simp [degreeIn]

theorem degreeIn_cons_ne {y : Var} {f : Nat} {t : Monomial} {x : Var} (h : y ≠ x) :
    degreeIn ((y, f) :: t) x = degreeIn t x := by
  simp [degreeIn, List.find?_cons_of_neg, h]

theorem degreeIn_eq_zero {m : Monomial} {x : Var} (h : ∀ p ∈ m, p.1 ≠ x) :
    degreeIn m x = 0 := by
  have hfind : m.find? (fun p => p.1 == x) = none :=
    List.find?_eq_none.mpr fun p hp => by simpa using h p hp
  simp [degreeIn, hfind]

/-- Every key of a merge-product is a key of one of the inputs; stated as
lower-bound transfer, which is what `Pairwise.cons` reconstruction needs. -/
theorem mul_keys_lb {v : Nat} {m n : Monomial} :
    (∀ p ∈ m, v < p.1) → (∀ p ∈ n, v < p.1) → ∀ p ∈ Monomial.mul m n, v < p.1 := by
  fun_induction Monomial.mul m n with
  | case1 n => intro _ hn; exact hn
  | case2 m _ => intro hm _; exact hm
  | case3 x e m y f n hxy ih =>
    intro hm hn p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact hm (x, e) (by simp)
    · exact ih (fun q hq => hm q (List.mem_cons_of_mem _ hq)) hn p hmem
  | case4 x e m y f n hxy hyx ih =>
    intro hm hn p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact hn (y, f) (by simp)
    · exact ih hm (fun q hq => hn q (List.mem_cons_of_mem _ hq)) p hmem
  | case5 x e m y f n hxy hyx ih =>
    intro hm hn p hp
    rcases List.mem_cons.mp hp with rfl | hmem
    · exact hm (x, e) (by simp)
    · exact ih (fun q hq => hm q (List.mem_cons_of_mem _ hq))
        (fun q hq => hn q (List.mem_cons_of_mem _ hq)) p hmem

theorem mul_canon {m n : Monomial} : Canon m → Canon n → Canon (Monomial.mul m n) := by
  fun_induction Monomial.mul m n with
  | case1 n => intro _ hn; exact hn
  | case2 m _ => intro hm _; exact hm
  | case3 x e m y f n hxy ih =>
    intro hm hn
    obtain ⟨hmp, hme⟩ := hm
    have hmt : Canon m :=
      ⟨(List.pairwise_cons.mp hmp).2, fun p hp => hme p (List.mem_cons_of_mem _ hp)⟩
    have ihc := ih hmt ⟨hn.1, hn.2⟩
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, ?_⟩
    · refine mul_keys_lb (fun q hq => (List.pairwise_cons.mp hmp).1 q hq) ?_
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hqm
      · exact hxy
      · exact Nat.lt_trans hxy ((List.pairwise_cons.mp hn.1).1 q hqm)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact hme (x, e) (by simp)
      · exact ihc.2 p hmem
  | case4 x e m y f n hxy hyx ih =>
    intro hm hn
    obtain ⟨hnp, hne⟩ := hn
    have hnt : Canon n :=
      ⟨(List.pairwise_cons.mp hnp).2, fun p hp => hne p (List.mem_cons_of_mem _ hp)⟩
    have ihc := ih ⟨hm.1, hm.2⟩ hnt
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, ?_⟩
    · refine mul_keys_lb ?_ (fun q hq => (List.pairwise_cons.mp hnp).1 q hq)
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hqm
      · exact hyx
      · exact Nat.lt_trans hyx ((List.pairwise_cons.mp hm.1).1 q hqm)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · exact hne (y, f) (by simp)
      · exact ihc.2 p hmem
  | case5 x e m y f n hxy hyx ih =>
    intro hm hn
    have hxey : x = y := Nat.le_antisymm (Nat.not_lt.mp hyx) (Nat.not_lt.mp hxy)
    subst hxey
    obtain ⟨hmp, hme⟩ := hm
    obtain ⟨hnp, hne⟩ := hn
    have hmt : Canon m :=
      ⟨(List.pairwise_cons.mp hmp).2, fun p hp => hme p (List.mem_cons_of_mem _ hp)⟩
    have hnt : Canon n :=
      ⟨(List.pairwise_cons.mp hnp).2, fun p hp => hne p (List.mem_cons_of_mem _ hp)⟩
    have ihc := ih hmt hnt
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, ?_⟩
    · exact mul_keys_lb (fun q hq => (List.pairwise_cons.mp hmp).1 q hq)
        (fun q hq => (List.pairwise_cons.mp hnp).1 q hq)
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · have he : 0 < e := hme (x, e) (by simp)
        show 0 < e + f
        omega
      · exact ihc.2 p hmem

/-- Exponents add under the sorted merge (needs sortedness of both inputs
so that a head variable is absent from the other side's tail). -/
theorem degreeIn_mul {m n : Monomial} :
    m.Pairwise (fun p q => p.1 < q.1) → n.Pairwise (fun p q => p.1 < q.1) →
    ∀ (v : Var), degreeIn (Monomial.mul m n) v = degreeIn m v + degreeIn n v := by
  fun_induction Monomial.mul m n with
  | case1 n => intro _ _ v; simp [degreeIn_nil]
  | case2 m _ => intro _ _ v; simp [degreeIn_nil]
  | case3 x e m y f n hxy ih =>
    intro hm hn v
    have hmt := (List.pairwise_cons.mp hm).2
    by_cases hv : v = x
    · subst hv
      have h0 : degreeIn ((y, f) :: n) v = 0 := degreeIn_eq_zero (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact (Nat.ne_of_lt hxy).symm
        · exact (Nat.ne_of_lt (Nat.lt_trans hxy ((List.pairwise_cons.mp hn).1 p hmem))).symm)
      rw [degreeIn_cons_self, degreeIn_cons_self, h0]
      omega
    · rw [degreeIn_cons_ne (Ne.symm hv), degreeIn_cons_ne (Ne.symm hv), ih hmt hn v]
  | case4 x e m y f n hxy hyx ih =>
    intro hm hn v
    have hnt := (List.pairwise_cons.mp hn).2
    by_cases hv : v = y
    · subst hv
      have h0 : degreeIn ((x, e) :: m) v = 0 := degreeIn_eq_zero (by
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hmem
        · exact (Nat.ne_of_lt hyx).symm
        · exact (Nat.ne_of_lt (Nat.lt_trans hyx ((List.pairwise_cons.mp hm).1 p hmem))).symm)
      rw [degreeIn_cons_self, degreeIn_cons_self, h0]
      omega
    · rw [degreeIn_cons_ne (Ne.symm hv), degreeIn_cons_ne (Ne.symm hv), ih hm hnt v]
  | case5 x e m y f n hxy hyx ih =>
    intro hm hn v
    have hxey : x = y := Nat.le_antisymm (Nat.not_lt.mp hyx) (Nat.not_lt.mp hxy)
    subst hxey
    have hmt := (List.pairwise_cons.mp hm).2
    have hnt := (List.pairwise_cons.mp hn).2
    by_cases hv : v = x
    · subst hv
      rw [degreeIn_cons_self, degreeIn_cons_self, degreeIn_cons_self]
    · rw [degreeIn_cons_ne (Ne.symm hv), degreeIn_cons_ne (Ne.symm hv),
          degreeIn_cons_ne (Ne.symm hv), ih hmt hnt v]

/-! ### Dense exponent-vector characterization

`denseCompare m n K` compares `degreeIn` from variable `K-1` down to `0` —
the exponent-vector reading of "biggest variable dominates". On canonical
(descending) lists with all keys `< K`, `lexCompare.go` computes exactly
this. Because `degreeIn` is representation-order-free, the sparse-merge
lemma `degreeIn_mul` then turns `cmp_mul_left` into pure `Nat.compare`
translation-invariance. -/

/-- Proof-layer only (not ported surface): dense top-down comparison. -/
def denseCompare (m n : Monomial) : Nat → Ordering
  | 0 => .eq
  | k + 1 =>
    match compare (degreeIn m k) (degreeIn n k) with
    | .eq => denseCompare m n k
    | o => o

theorem denseCompare_congr {a a' b b' : Monomial} :
    ∀ (K : Nat), (∀ j, j < K → degreeIn a j = degreeIn a' j) →
      (∀ j, j < K → degreeIn b j = degreeIn b' j) →
      denseCompare a b K = denseCompare a' b' K
  | 0, _, _ => rfl
  | K + 1, ha, hb => by
    simp only [denseCompare, ha K (by omega), hb K (by omega)]
    cases compare (degreeIn a' K) (degreeIn b' K) <;>
      simp [denseCompare_congr K (fun j hj => ha j (by omega)) (fun j hj => hb j (by omega))]

/-- If a descending list bounded by `< k+1` is not bounded by `< k`, its
head variable is exactly `k`. -/
theorem head_key_eq {b : Monomial} {k : Nat}
    (hdb : b.Pairwise (fun s q => q.1 < s.1))
    (hbK : ∀ p ∈ b, p.1 < k + 1) (hbk : ¬ ∀ p ∈ b, p.1 < k) :
    ∃ f n, b = (k, f) :: n := by
  push_neg at hbk
  obtain ⟨p, hpmem, hpk⟩ := hbk
  cases b with
  | nil => simp at hpmem
  | cons q n =>
    obtain ⟨y, f⟩ := q
    have hy : y < k + 1 := hbK (y, f) (by simp)
    have hyk : y = k := by
      rcases List.mem_cons.mp hpmem with rfl | hmem
      · exact Nat.le_antisymm (Nat.le_of_lt_succ hy) hpk
      · have h1 : p.1 < y := (List.pairwise_cons.mp hdb).1 p hmem
        exact absurd (Nat.lt_of_le_of_lt hpk h1) (Nat.not_lt.mpr (Nat.le_of_lt_succ hy))
    exact ⟨f, n, by rw [hyk]⟩

/-- The characterization: on descending, positive-exponent lists with all
keys `< K`, `go` computes the dense top-down comparison. -/
theorem go_eq_dense (K : Nat) : ∀ {a b : Monomial},
    a.Pairwise (fun s q => q.1 < s.1) → b.Pairwise (fun s q => q.1 < s.1) →
    (∀ p ∈ a, 0 < p.2) → (∀ p ∈ b, 0 < p.2) →
    (∀ p ∈ a, p.1 < K) → (∀ p ∈ b, p.1 < K) →
    lexCompare.go a b = denseCompare a b K := by
  induction K with
  | zero =>
    intro a b _ _ _ _ haK hbK
    cases a with
    | cons p t => exact absurd (haK p (by simp)) (Nat.not_lt_zero _)
    | nil =>
      cases b with
      | cons q t => exact absurd (hbK q (by simp)) (Nat.not_lt_zero _)
      | nil => rfl
  | succ k ih =>
    intro a b hda hdb hea heb haK hbK
    by_cases hak : ∀ p ∈ a, p.1 < k <;> by_cases hbk : ∀ p ∈ b, p.1 < k
    · -- no key reaches k on either side: dense layer is 0-vs-0, recurse
      have ha0 : degreeIn a k = 0 := degreeIn_eq_zero fun p hp => Nat.ne_of_lt (hak p hp)
      have hb0 : degreeIn b k = 0 := degreeIn_eq_zero fun p hp => Nat.ne_of_lt (hbk p hp)
      rw [ih hda hdb hea heb hak hbk]
      simp only [denseCompare, ha0, hb0]
      rfl
    · -- b's head is exactly k, a is entirely below: `.lt`
      obtain ⟨f, n, rfl⟩ := head_key_eq hdb hbK hbk
      have ha0 : degreeIn a k = 0 := degreeIn_eq_zero fun p hp => Nat.ne_of_lt (hak p hp)
      have hf : 0 < f := heb (k, f) (by simp)
      have hcmp : compare (0 : Nat) f = .lt := Nat.compare_eq_lt.mpr hf
      simp only [denseCompare, ha0, degreeIn_cons_self, hcmp]
      exact go_lt_of_keys_lt fun p hp => hak p hp
    · -- a's head is exactly k, b is entirely below: `.gt`
      obtain ⟨e, a', rfl⟩ := head_key_eq hda haK hak
      have hb0 : degreeIn b k = 0 := degreeIn_eq_zero fun p hp => Nat.ne_of_lt (hbk p hp)
      have he : 0 < e := hea (k, e) (by simp)
      have hcmp : compare e (0 : Nat) = .gt := Nat.compare_eq_gt.mpr he
      simp only [denseCompare, hb0, degreeIn_cons_self, hcmp]
      exact go_gt_of_keys_lt fun p hp => hbk p hp
    · -- both heads are exactly k: exponent showdown
      obtain ⟨e, a', rfl⟩ := head_key_eq hda haK hak
      obtain ⟨f, n', rfl⟩ := head_key_eq hdb hbK hbk
      have hda' := (List.pairwise_cons.mp hda).2
      have hdb' := (List.pairwise_cons.mp hdb).2
      have haK' : ∀ p ∈ a', p.1 < k := fun p hp => (List.pairwise_cons.mp hda).1 p hp
      have hbK' : ∀ p ∈ n', p.1 < k := fun p hp => (List.pairwise_cons.mp hdb).1 p hp
      have hea' : ∀ p ∈ a', 0 < p.2 := fun p hp => hea p (List.mem_cons_of_mem _ hp)
      have heb' : ∀ p ∈ n', 0 < p.2 := fun p hp => heb p (List.mem_cons_of_mem _ hp)
      by_cases hef : e = f
      · subst hef
        have h1 : lexCompare.go ((k, e) :: a') ((k, e) :: n') = lexCompare.go a' n' := by
          simp [lexCompare.go]
        have hcongr := denseCompare_congr (a := a') (a' := (k, e) :: a')
          (b := n') (b' := (k, e) :: n') k
          (fun j hj => (degreeIn_cons_ne (show k ≠ j by omega)).symm)
          (fun j hj => (degreeIn_cons_ne (show k ≠ j by omega)).symm)
        rw [h1, ih hda' hdb' hea' heb' haK' hbK']
        simp only [denseCompare, degreeIn_cons_self]
        rw [show compare e e = Ordering.eq from Nat.compare_eq_eq.mpr rfl]
        exact hcongr
      · have h1 : lexCompare.go ((k, e) :: a') ((k, f) :: n') = compare e f := by
          rcases Nat.lt_trichotomy e f with h | h | h
          · simp [lexCompare.go, hef, h, Nat.compare_eq_lt.mpr h]
          · exact absurd h hef
          · simp [lexCompare.go, hef, Nat.lt_asymm h, Nat.compare_eq_gt.mpr h]
        rw [h1]
        simp only [denseCompare, degreeIn_cons_self]
        cases hc : compare e f with
        | eq => exact absurd (Nat.compare_eq_eq.mp hc) hef
        | lt => rfl
        | gt => rfl

/-! ### Transport through the reversal -/

/-- `find?` by key is reversal-invariant when keys are distinct. -/
theorem find?_key_reverse {m : Monomial}
    (hnd : m.Pairwise (fun p q => p.1 ≠ q.1)) (x : Var) :
    m.reverse.find? (fun p => p.1 == x) = m.find? (fun p => p.1 == x) := by
  induction m with
  | nil => rfl
  | cons p t ih =>
    have hp := (List.pairwise_cons.mp hnd).1
    have ht := (List.pairwise_cons.mp hnd).2
    rw [List.reverse_cons, List.find?_append, ih ht]
    by_cases hx : p.1 = x
    · have htn : t.find? (fun q => q.1 == x) = none :=
        List.find?_eq_none.mpr fun q hq => by
          have hne : p.1 ≠ q.1 := hp q hq
          simp only [beq_iff_eq]
          exact fun heq => hne (hx.trans heq.symm)
      simp [htn, List.find?_cons_of_pos, hx]
    · simp [List.find?_cons_of_neg, hx, Option.or_none]

theorem degreeIn_reverse {m : Monomial}
    (h : m.Pairwise (fun p q => p.1 < q.1)) (x : Var) :
    degreeIn m.reverse x = degreeIn m x := by
  have hnd : m.Pairwise (fun p q => p.1 ≠ q.1) := h.imp fun hlt => Nat.ne_of_lt hlt
  simp only [degreeIn]
  rw [find?_key_reverse hnd]

theorem lexCompare_eq_dense {m n : Monomial} (K : Nat) (hm : Canon m) (hn : Canon n)
    (hmK : ∀ p ∈ m, p.1 < K) (hnK : ∀ p ∈ n, p.1 < K) :
    lexCompare m n = denseCompare m n K := by
  have hgo : lexCompare m n = lexCompare.go m.reverse n.reverse := rfl
  rw [hgo, go_eq_dense K (List.pairwise_reverse.mpr hm.1) (List.pairwise_reverse.mpr hn.1)
      (fun p hp => hm.2 p (List.mem_reverse.mp hp))
      (fun p hp => hn.2 p (List.mem_reverse.mp hp))
      (fun p hp => hmK p (List.mem_reverse.mp hp))
      (fun p hp => hnK p (List.mem_reverse.mp hp))]
  exact denseCompare_congr K (fun j _ => degreeIn_reverse hm.1 j)
    (fun j _ => degreeIn_reverse hn.1 j)

/-! ### The keystone: left-multiplication preserves the order verdict -/

/-- Strict upper bound on the variable indices of a monomial. -/
def varBound (m : Monomial) : Nat := m.foldr (fun p acc => max (p.1 + 1) acc) 0

theorem lt_varBound (m : Monomial) : ∀ p ∈ m, p.1 < varBound m := by
  induction m with
  | nil => simp
  | cons q t ih =>
    intro p hp
    rcases List.mem_cons.mp hp with heq | hmem
    · subst heq
      show p.1 < max (p.1 + 1) (varBound t)
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · show p.1 < max (q.1 + 1) (varBound t)
      exact Nat.lt_of_lt_of_le (ih p hmem) (Nat.le_max_right _ _)

theorem nat_compare_add_left (c a b : Nat) : compare (c + a) (c + b) = compare a b := by
  rcases Nat.lt_trichotomy a b with h | h | h
  · rw [Nat.compare_eq_lt.mpr h, Nat.compare_eq_lt.mpr (by omega)]
  · subst h; rw [Nat.compare_eq_eq.mpr rfl, Nat.compare_eq_eq.mpr rfl]
  · rw [Nat.compare_eq_gt.mpr h, Nat.compare_eq_gt.mpr (by omega)]

theorem denseCompare_mul_left {k m n : Monomial}
    (hk : k.Pairwise (fun p q => p.1 < q.1)) (hm : m.Pairwise (fun p q => p.1 < q.1))
    (hn : n.Pairwise (fun p q => p.1 < q.1)) :
    ∀ K, denseCompare (Monomial.mul k m) (Monomial.mul k n) K = denseCompare m n K := by
  intro K
  induction K with
  | zero => rfl
  | succ j ihK =>
    simp only [denseCompare, degreeIn_mul hk hm j, degreeIn_mul hk hn j,
      nat_compare_add_left]
    cases compare (degreeIn m j) (degreeIn n j) <;> simp [ihK]

/-- Multiplying on the left by a fixed canonical monomial preserves the
`cmp` verdict *as an equality* — the lex order is translation-invariant
on exponent vectors. This is what makes `MPoly.smulTerm`'s map preserve
strictly-descending storage order without the re-sort z3 performs
(`lex_sort`; z3 itself never carries sortedness through a product). -/
theorem cmp_mul_left {k m n : Monomial} (hk : Canon k) (hm : Canon m) (hn : Canon n) :
    cmp (Monomial.mul k m) (Monomial.mul k n) = cmp m n := by
  have h1 := lexCompare_eq_dense
    (varBound (Monomial.mul k m) + varBound (Monomial.mul k n) + varBound m + varBound n)
    (mul_canon hk hm) (mul_canon hk hn)
    (fun p hp => Nat.lt_of_lt_of_le (lt_varBound _ p hp) (by omega))
    (fun p hp => Nat.lt_of_lt_of_le (lt_varBound _ p hp) (by omega))
  have h2 := lexCompare_eq_dense
    (varBound (Monomial.mul k m) + varBound (Monomial.mul k n) + varBound m + varBound n)
    hm hn
    (fun p hp => Nat.lt_of_lt_of_le (lt_varBound _ p hp) (by omega))
    (fun p hp => Nat.lt_of_lt_of_le (lt_varBound _ p hp) (by omega))
  show lexCompare _ _ = lexCompare _ _
  rw [h1, h2]
  exact denseCompare_mul_left hk.1 hm.1 hn.1 _

end Monomial

/-! ### Canonical polynomials -/

namespace MPoly

/-- Canonical `MPoly`: nonzero coefficients, monomials strictly descending
in `Monomial.cmp` (z3 `m_lex_sorted` storage), each monomial canonical. -/
def Canon (p : MPoly) : Prop :=
  p.Pairwise (fun s t => Monomial.cmp s.2 t.2 = .gt) ∧
    ∀ t ∈ p, t.1 ≠ 0 ∧ Monomial.Canon t.2

theorem canon_nil : Canon [] := ⟨List.Pairwise.nil, by simp⟩

theorem zero_canon : Canon MPoly.zero := canon_nil

theorem ofInt_canon (n : Int) : Canon (MPoly.ofInt n) := by
  unfold MPoly.ofInt
  split
  · exact canon_nil
  · rename_i h
    refine ⟨List.pairwise_singleton _ _, ?_⟩
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨by simpa using h, Monomial.canon_nil⟩

theorem ofVar_canon (x : Var) : Canon (MPoly.ofVar x) := by
  refine ⟨List.pairwise_singleton _ _, ?_⟩
  intro t ht
  simp only [MPoly.ofVar, List.mem_singleton] at ht
  subst ht
  refine ⟨by simp, List.pairwise_singleton _ _, ?_⟩
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  simp

/-- Two-term canonicality constructor (covers the checker/test-suite
concrete polys): descending-ordered terms with nonzero canonical parts. -/
theorem canon_two (a : Int) (m : Monomial) (b : Int) (n : Monomial)
    (ha : a ≠ 0) (hm : Monomial.Canon m) (hb : b ≠ 0) (hn : Monomial.Canon n)
    (hgt : Monomial.cmp m n = .gt) : Canon [(a, m), (b, n)] :=
  ⟨List.pairwise_cons.mpr ⟨fun c hc => by
      rcases List.mem_singleton.mp hc with rfl
      exact hgt, List.pairwise_singleton _ _⟩,
    fun t ht => by
      rcases List.mem_cons.mp ht with rfl | h
      · exact ⟨ha, hm⟩
      · rcases List.mem_singleton.mp h with rfl
        exact ⟨hb, hn⟩⟩

/-- Merge-add respects a strict upper bound (in `cmp`) on the monomials —
the head-dominance transfer that rebuilds `Pairwise` through the merge. -/
theorem add_bound {mo : Monomial} {p q : MPoly} :
    (∀ t ∈ p, Monomial.cmp mo t.2 = .gt) → (∀ t ∈ q, Monomial.cmp mo t.2 = .gt) →
    ∀ t ∈ MPoly.add p q, Monomial.cmp mo t.2 = .gt := by
  fun_induction MPoly.add p q with
  | case1 q => intro _ hq; exact hq
  | case2 p _ => intro hp _; exact hp
  | case3 a m p b n q hcmp ih =>
    intro hp hq t ht
    rcases List.mem_cons.mp ht with rfl | hmem
    · exact hp (a, m) (by simp)
    · exact ih (fun s hs => hp s (List.mem_cons_of_mem _ hs)) hq t hmem
  | case4 a m p b n q hcmp ih =>
    intro hp hq t ht
    rcases List.mem_cons.mp ht with rfl | hmem
    · exact hq (b, n) (by simp)
    · exact ih hp (fun s hs => hq s (List.mem_cons_of_mem _ hs)) t hmem
  | case5 a m p b n q hcmp c hc ih =>
    intro hp hq
    exact ih (fun s hs => hp s (List.mem_cons_of_mem _ hs))
      (fun s hs => hq s (List.mem_cons_of_mem _ hs))
  | case6 a m p b n q hcmp c hc ih =>
    intro hp hq t ht
    rcases List.mem_cons.mp ht with rfl | hmem
    · exact hp (a, m) (by simp)
    · exact ih (fun s hs => hp s (List.mem_cons_of_mem _ hs))
        (fun s hs => hq s (List.mem_cons_of_mem _ hs)) t hmem

theorem add_canon {p q : MPoly} : Canon p → Canon q → Canon (MPoly.add p q) := by
  fun_induction MPoly.add p q with
  | case1 q => intro _ hq; exact hq
  | case2 p _ => intro hp _; exact hp
  | case3 a m p b n q hcmp ih =>
    intro hp hq
    obtain ⟨hpw, hpe⟩ := hp
    have hpt : Canon p :=
      ⟨(List.pairwise_cons.mp hpw).2, fun t ht => hpe t (List.mem_cons_of_mem _ ht)⟩
    have ihc := ih hpt hq
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, ?_⟩
    · refine add_bound (fun t ht => (List.pairwise_cons.mp hpw).1 t ht) ?_
      intro t ht
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hcmp
      · exact Monomial.cmp_gt_trans hcmp ((List.pairwise_cons.mp hq.1).1 t hmem)
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hpe (a, m) (by simp)
      · exact ihc.2 t hmem
  | case4 a m p b n q hcmp ih =>
    intro hp hq
    obtain ⟨hqw, hqe⟩ := hq
    have hqt : Canon q :=
      ⟨(List.pairwise_cons.mp hqw).2, fun t ht => hqe t (List.mem_cons_of_mem _ ht)⟩
    have ihc := ih hp hqt
    have hnm : Monomial.cmp n m = .gt := by rw [Monomial.cmp_swap, hcmp]; rfl
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, ?_⟩
    · refine add_bound ?_ (fun t ht => (List.pairwise_cons.mp hqw).1 t ht)
      intro t ht
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hnm
      · exact Monomial.cmp_gt_trans hnm ((List.pairwise_cons.mp hp.1).1 t hmem)
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | hmem
      · exact hqe (b, n) (by simp)
      · exact ihc.2 t hmem
  | case5 a m p b n q hcmp c hc ih =>
    intro hp hq
    exact ih ⟨(List.pairwise_cons.mp hp.1).2, fun t ht => hp.2 t (List.mem_cons_of_mem _ ht)⟩
      ⟨(List.pairwise_cons.mp hq.1).2, fun t ht => hq.2 t (List.mem_cons_of_mem _ ht)⟩
  | case6 a m p b n q hcmp c hc ih =>
    intro hp hq
    have hmn : m = n := Monomial.cmp_eq_iff.mp hcmp
    subst hmn
    obtain ⟨hpw, hpe⟩ := hp
    obtain ⟨hqw, hqe⟩ := hq
    have hpt : Canon p :=
      ⟨(List.pairwise_cons.mp hpw).2, fun t ht => hpe t (List.mem_cons_of_mem _ ht)⟩
    have hqt : Canon q :=
      ⟨(List.pairwise_cons.mp hqw).2, fun t ht => hqe t (List.mem_cons_of_mem _ ht)⟩
    have ihc := ih hpt hqt
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, ?_⟩
    · exact add_bound (fun t ht => (List.pairwise_cons.mp hpw).1 t ht)
        (fun t ht => (List.pairwise_cons.mp hqw).1 t ht)
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | hmem
      · refine ⟨?_, (hpe (a, m) (by simp)).2⟩
        show a + b ≠ 0
        simpa using hc
      · exact ihc.2 t hmem

theorem neg_canon {p : MPoly} (hp : Canon p) : Canon (MPoly.neg p) := by
  obtain ⟨hw, he⟩ := hp
  constructor
  · simp only [MPoly.neg]
    refine List.pairwise_map.mpr (hw.imp fun {s t} h => ?_)
    obtain ⟨a, m⟩ := s; obtain ⟨b, n⟩ := t
    exact h
  · intro t ht
    simp only [MPoly.neg, List.mem_map] at ht
    obtain ⟨⟨a, m⟩, hmem, rfl⟩ := ht
    refine ⟨?_, (he (a, m) hmem).2⟩
    have ha : a ≠ 0 := (he (a, m) hmem).1
    show -a ≠ 0
    omega

theorem sub_canon {p q : MPoly} (hp : Canon p) (hq : Canon q) : Canon (MPoly.sub p q) :=
  add_canon hp (neg_canon hq)

theorem smulTerm_canon {c : Int} {mo : Monomial} {p : MPoly}
    (hmo : Monomial.Canon mo) (hp : Canon p) : Canon (MPoly.smulTerm c mo p) := by
  obtain ⟨hw, he⟩ := hp
  unfold MPoly.smulTerm
  split
  · exact canon_nil
  · rename_i hc
    have hc' : c ≠ 0 := by simpa using hc
    constructor
    · refine List.pairwise_map.mpr (List.Pairwise.imp_of_mem ?_ hw)
      intro s t hs ht h
      obtain ⟨a, m⟩ := s; obtain ⟨b, n⟩ := t
      show Monomial.cmp (Monomial.mul mo m) (Monomial.mul mo n) = .gt
      rw [Monomial.cmp_mul_left hmo (he (a, m) hs).2 (he (b, n) ht).2]
      exact h
    · intro t ht
      simp only [List.mem_map] at ht
      obtain ⟨⟨a, m⟩, hmem, rfl⟩ := ht
      refine ⟨?_, Monomial.mul_canon hmo (he (a, m) hmem).2⟩
      show c * a ≠ 0
      exact Int.mul_ne_zero hc' (he (a, m) hmem).1

theorem mul_canon {p q : MPoly} (hp : Canon p) (hq : Canon q) : Canon (MPoly.mul p q) := by
  suffices h : ∀ (l : MPoly), (∀ t ∈ l, t.1 ≠ 0 ∧ Monomial.Canon t.2) →
      ∀ acc, Canon acc →
      Canon (List.foldl (fun acc t => MPoly.add acc (MPoly.smulTerm t.1 t.2 q)) acc l) by
    exact h p hp.2 [] canon_nil
  intro l
  induction l with
  | nil => intro _ acc hacc; simpa using hacc
  | cons t l' ihl =>
    intro hl acc hacc
    simp only [List.foldl_cons]
    exact ihl (fun s hs => hl s (List.mem_cons_of_mem _ hs)) _
      (add_canon hacc (smulTerm_canon (hl t (by simp)).2 hq))

end MPoly

/-! ### Decidable canonicity mirrors (G4 census — the checker boundary's
`decide` ticket)

`MPoly.Canon` is a `Prop` (pairwise comparisons + pointwise
nonzero/canonical conditions); the checker's step consumption needs
`Canon` evidence from CONCRETE payload polys at decide grade. Since
`MPoly.add` is wf-compiled (not kernel-reducible), no `decide` route
through polynomial arithmetic can work — but canonicity is a pure
LIST condition, so a structural Boolean mirror + soundness theorems
close the gap. The head-vs-head strict-increase checks suffice:
each condition plus the tail's own canonicity gives the full pairwise
order by order transitivity. -/

namespace Monomial

/-- Decidable mirror of `Monomial.Canon`. -/
def canonOK : Monomial → Bool
  | [] => true
  | (x, e) :: m =>
    decide (0 < e) &&
    (match m with
     | [] => true
     | (x', _) :: _ => decide (x < x')) &&
    canonOK m

theorem canonOK_sound : ∀ m : Monomial, canonOK m = true → Canon m
  | [], _ => canon_nil
  | (x, e) :: m, h => by
    unfold canonOK at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨he, hhead⟩, hrest⟩ := h
    have ihc := canonOK_sound m hrest
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, fun p hp => ?_⟩
    · intro p hp
      cases m with
      | nil => simp at hp
      | cons x'e' m' =>
        obtain ⟨x', e'⟩ := x'e'
        have hx : x < x' := of_decide_eq_true hhead
        rcases List.mem_cons.mp hp with rfl | hpm
        · exact hx
        · have h1 : x' < p.1 := (List.pairwise_cons.mp ihc.1).1 p hpm
          exact Nat.lt_trans hx h1
    · rw [List.mem_cons] at hp
      rcases hp with rfl | hpm
      · exact of_decide_eq_true he
      · exact ihc.2 p hpm

end Monomial

namespace MPoly

/-- Decidable mirror of `MPoly.Canon`. -/
def canonOK : MPoly → Bool
  | [] => true
  | (a, m) :: p =>
    decide (a ≠ 0) && m.canonOK &&
    (match p with
     | [] => true
     | (_, n) :: _ => decide (Monomial.cmp m n = .gt)) &&
    canonOK p

theorem canonOK_sound : ∀ p : MPoly, canonOK p = true → Canon p
  | [], _ => canon_nil
  | (a, m) :: p, h => by
    unfold canonOK at h
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨⟨ha, hm⟩, hhead⟩, hrest⟩ := h
    have ihc := canonOK_sound p hrest
    have hmc := Monomial.canonOK_sound m hm
    refine ⟨List.pairwise_cons.mpr ⟨?_, ihc.1⟩, fun t ht => ?_⟩
    · intro t ht
      cases p with
      | nil => simp at ht
      | cons bn p' =>
        obtain ⟨b, n⟩ := bn
        have hc : Monomial.cmp m n = .gt := of_decide_eq_true hhead
        rcases List.mem_cons.mp ht with rfl | htm
        · exact hc
        · exact Monomial.cmp_gt_trans hc ((List.pairwise_cons.mp ihc.1).1 t htm)
    · rcases List.mem_cons.mp ht with rfl | htm
      · exact ⟨of_decide_eq_true ha, hmc⟩
      · exact ihc.2 t htm

end MPoly

/-! ### Pins (the docstring ordering chain, `polynomial.cpp:625` reading) -/

-- x₃³ > x₃²x₁² > x₃x₂²x₁ > x₁³
#guard Monomial.cmp [(3, 3)] [(1, 2), (3, 2)] == .gt
#guard Monomial.cmp [(1, 2), (3, 2)] [(1, 1), (2, 2), (3, 1)] == .gt
#guard Monomial.cmp [(1, 1), (2, 2), (3, 1)] [(1, 3)] == .gt
-- swap duality on a concrete pair
#guard Monomial.cmp [(1, 3)] [(1, 1), (2, 2), (3, 1)] == .lt

end LeanNonlinearArith.Nlsat
