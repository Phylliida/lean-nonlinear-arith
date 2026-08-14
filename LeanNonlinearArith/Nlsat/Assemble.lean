import LeanNonlinearArith.Nlsat.Coverage

/-!
# nla-19a Slice F — checker assembly: decode + the propositional engine (TRUSTED)

The F2-seam decode (F1) and the propositional replay engine (the R1
resolution glue, F3's heart). Two layers:

1. **Decode (F1).** Solver-level literals/clauses get their semantics
   through the atom table snapshot (`Solver.refutation`, captured
   pre-`restoreOrder` in internal variable order): `litHolds` /
   `clauseHolds`, with the `interp` bridge to the interpretation form
   `litSatI`/`clauseSatI` the propositional engine is proved against.
   Undecodable bvars count as NOT holding (the sound direction — they
   only make `clauseHolds` harder to establish). `Atom.bool` proxy
   slots (nla-14 Tseitin) decode through their definitions
   (`boolDefHolds`, flattened/arith-only leaves); the `BoolDef.eval` /
   `taut`/`conseq` reflection discharges definitional and root clause
   bridges by `decide`-grade computation (`taut_sound`/`conseq_sound`,
   axioms propext/choice/Quot.sound only).

2. **The unit-propagation (RUP) engine (R1/F3).** Each bundle's learned
   lemma follows from its antecedent clauses + arith lemmas by
   tauto-grade composition; the final bundle's empty lemma closes the
   refutation. The checker is `upRefutes F target`: negate `target`'s
   literals as units, propagate to closure, look for a falsified
   clause. `upRefutes_sound` is the only property the trusted layer
   needs (completeness for z3's resolution chains is the reverse-
   induction RUP argument — recorded in the BOARD; a stall is a sound
   rejection). All junk paths (out-of-range bvars, dropped units,
   fuel exhaustion) fail toward `false` = rejection.

The per-bundle ARITH validity (F2 — discharging each
`resolution (.arith core proj)` marker's clause `proj ++ ¬core` from
the bundle's projection steps via `Nlsat/Coverage.lean`) and the
top-level DAG walk + elaborator land next; this file is their engine.
-/

namespace LeanNonlinearArith.Nlsat

open Check

/-! ## Decode (F1) -/

/-- Literal satisfaction under an atom interpretation. -/
def litSatI (I : Nat → Prop) (l : Literal) : Prop :=
  if l.neg then ¬ I l.bvar else I l.bvar

/-- Clause satisfaction: some literal holds. -/
def clauseSatI (I : Nat → Prop) (C : List Literal) : Prop :=
  ∃ l ∈ C, litSatI I l

/-- R2' hardening (review 14): literal `dedup` is a semantic identity —
`List.mem_dedup` preserves membership both ways. (`dedup` is native-
AND kernel-computable on concrete literal lists — probed 2026-08-10,
`example : ([⟨0,false⟩,⟨0,false⟩] : List Literal).dedup = _ := rfl`.) -/
theorem clauseSatI_dedup (I : Nat → Prop) (C : List Literal) :
    clauseSatI I C.dedup ↔ clauseSatI I C :=
  exists_congr fun l => and_congr List.mem_dedup Iff.rfl

/-- The ∀ side of the same bridge. -/
theorem not_litSatI_forall_dedup (I : Nat → Prop) (C : List Literal) :
    (∀ l ∈ C, ¬ litSatI I l) → ∀ l ∈ C.dedup, ¬ litSatI I l :=
  fun h l hl => h l (List.mem_dedup.mp hl)

/-- Table-level semantics of a proxy definition (nla-14). Leaves may
reference OTHER PROXIES — z3's Tseitin nests, and the sharing is the
point (defs stay small; the definitional-clause checks stay local).
Proxy chasing descends the atom table guarded by a BOUND: a proxy leaf
may unfold only to a strictly SMALLER bvar (`bound` starts at
`atoms.size` in `interp`/`litHolds`). Conformant tables — defs
reference strictly smaller bvars (Tseitin emission order) — evaluate
exactly as intended; forward/cyclic references hit the bound guard and
poison to `False` (the sound direction). The bound makes evaluation
PATH-INDEPENDENT: entering proxy `p`'s def always recurses at bound
`p`, no matter where the path started (`boolDefHolds_irrel`). -/
def boolDefHolds (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (bound : Nat) (d : BoolDef) : Prop :=
  match d with
  | .lit l =>
    match atoms[l.bvar]? with
    | some (some (.bool d')) =>
      if h : l.bvar < bound then
        (if l.neg then ¬ boolDefHolds ρ atoms l.bvar d'
         else boolDefHolds ρ atoms l.bvar d')
      else False
    | some (some a) => ALitHolds ρ a l.neg
    | _ => False
  | .and a b => boolDefHolds ρ atoms bound a ∧ boolDefHolds ρ atoms bound b
  | .or a b => boolDefHolds ρ atoms bound a ∨ boolDefHolds ρ atoms bound b
  | .neg a => ¬ boolDefHolds ρ atoms bound a
  | .tru => True
  | .fls => False
termination_by (bound, d)

/-- The atom-table interpretation: bvar `b` holds iff the table maps it
to an atom that holds at `ρ`; a proxy (`Atom.bool`) holds iff its
definition does (fuel = table size: conformant acyclic chains have
depth ≤ #proxies ≤ size, and the `.lit`-proxy step's decrement matches
the `litHolds`-bridge lemmas' fuel flow). Undecodable ↦ `False`
(sound direction). -/
def interp (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (b : Nat) : Prop :=
  match atoms[b]? with
  | some (some (.bool d)) => boolDefHolds ρ atoms atoms.size d
  | some (some a) => Atom.Holds ρ a
  | _ => False

/-- Solver-level literal semantics (the F2 extraction's form). -/
def litHolds (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (l : Literal) : Prop :=
  match atoms[l.bvar]? with
  | some (some (.bool d)) => if l.neg then ¬ boolDefHolds ρ atoms atoms.size d
                             else boolDefHolds ρ atoms atoms.size d
  | some (some a) => ALitHolds ρ a l.neg
  | _ => False

/-- Solver-level clause semantics. -/
def clauseHolds (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (C : List Literal) : Prop :=
  ∃ l ∈ C, litHolds ρ atoms l

/-- The two literal semantics agree on decodable literals (on junk
they intentionally differ: `litHolds` is `False` either polarity — the
sound direction — while `litSatI` negates the junk value). -/
theorem litSatI_interp (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (l : Literal)
    (hdec : ∃ a, atoms[l.bvar]? = some (some a)) :
    litSatI (interp ρ atoms) l ↔ litHolds ρ atoms l := by
  obtain ⟨a, ha⟩ := hdec
  obtain ⟨b, n⟩ := l
  cases a <;> cases n <;> simp [litSatI, litHolds, interp, ALitHolds, ha]

theorem clauseSatI_interp (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (C : List Literal)
    (hdec : ∀ l ∈ C, ∃ a, atoms[l.bvar]? = some (some a)) :
    clauseSatI (interp ρ atoms) C ↔ clauseHolds ρ atoms C := by
  unfold clauseSatI clauseHolds
  constructor
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, (litSatI_interp ρ atoms l (hdec l hl)).mp h⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨l, hl, (litSatI_interp ρ atoms l (hdec l hl)).mpr h⟩

/-- The arith lemma of a `.arith core proj` marker, as a clause
(`resolve_lazy_justification`, Solver.lean:917-921: `proj ++ ¬core`). -/
def arithClause (core proj : List Literal) : List Literal :=
  proj ++ core.map Literal.negate

/-- Negated clause ⇒ every literal fails (the `ht` side of the RUP
application for learned clauses in the F3 walk). -/
theorem not_litSatI_forall_of_not_clauseSatI {I : Nat → Prop} {C : List Literal}
    (h : ¬ clauseSatI I C) : ∀ l ∈ C, ¬ litSatI I l :=
  fun l hl hls => h ⟨l, hl, hls⟩

/-- Per-clause decodability check (kernel-computable: literal-array
lookups + Bool only). -/
def clauseDecodable (atoms : Array (Option Atom)) : List Literal → Bool
  | [] => true
  | l :: ls =>
    (match atoms[l.bvar]? with | some (some _) => true | _ => false) &&
    clauseDecodable atoms ls

/-- The check implies the per-literal decodability `clauseSatI_interp`
consumes (the F3 walk's bridge hypotheses enter as
`clauseDecodable_true … (by decide)`). -/
theorem clauseDecodable_true (atoms : Array (Option Atom)) :
    ∀ C : List Literal, clauseDecodable atoms C = true →
      ∀ l ∈ C, ∃ a, atoms[l.bvar]? = some (some a) := by
  intro C
  induction C with
  | nil => intro _ l hl; cases hl
  | cons l ls ih =>
    intro h l' hl'
    unfold clauseDecodable at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases hl' with
    | head =>
      split at h1
      · rename_i a ha; exact ⟨a, ha⟩
      · simp at h1
    | tail _ hm => exact ih h2 l' hm

/-! ## The Boolean-form reflection (nla-14 Slice 1: Tseitin proxy bridges)

Definitional and root clauses over proxies unfold (via `boolDefHolds`)
to propositional formulas over literals — with child proxies ABSTRACT
(hierarchical defs, R-i of the design review: each definitional clause
checks locally over its ≤ handful of leaves, never the inlined
subtree). `BoolDef.taut` enumerates the valuations of the leaves and
`taut_sound`/`conseq_sound` reflect a `true` verdict into
`BoolDef.eval` under ANY oracle — instantiated at the leaf semantics,
this discharges the bridge. All junk paths fail toward `false` =
rejection, same as the UP engine. -/

namespace BoolDef

open Classical

/-- Propositional evaluation under a literal oracle. -/
def eval (τ : Literal → Prop) : BoolDef → Prop
  | .lit l => τ l
  | .and a b => eval τ a ∧ eval τ b
  | .or a b => eval τ a ∨ eval τ b
  | .neg a => ¬ eval τ a
  | .tru => True
  | .fls => False

/-- `boolDefHolds` IS `eval` at the leaf-semantics oracle (the bridge
the discharges consume — proxy leaves abstract, so the `taut` checks
stay local to each definitional clause). -/
theorem boolDefHolds_iff_eval (ρ : Nat → ℝ) (atoms : Array (Option Atom)) :
    ∀ (fuel : Nat) (d : BoolDef), boolDefHolds ρ atoms fuel d ↔
      eval (fun l => boolDefHolds ρ atoms fuel (.lit l)) d := by
  intro fuel d
  induction d with
  | lit l => exact Iff.rfl
  | and a b iha ihb =>
    simp only [boolDefHolds] at iha ihb ⊢; exact and_congr iha ihb
  | or a b iha ihb =>
    simp only [boolDefHolds] at iha ihb ⊢; exact or_congr iha ihb
  | neg a ih =>
    simp only [boolDefHolds] at ih ⊢; exact not_congr ih
  | tru => simp only [boolDefHolds]; exact Iff.rfl
  | fls => simp only [boolDefHolds]; exact Iff.rfl

/-- Computable evaluation under a Boolean assignment. -/
def evalB (σ : Literal → Bool) : BoolDef → Bool
  | .lit l => σ l
  | .and a b => evalB σ a && evalB σ b
  | .or a b => evalB σ a || evalB σ b
  | .neg a => !evalB σ a
  | .tru => true
  | .fls => false

/-- The leaf literals, in occurrence order. -/
def leaves : BoolDef → List Literal
  | .lit l => [l]
  | .and a b => leaves a ++ leaves b
  | .or a b => leaves a ++ leaves b
  | .neg a => leaves a
  | .tru => []
  | .fls => []

/-- `evalB` depends only on the leaves. -/
theorem evalB_ext {σ₁ σ₂ : Literal → Bool} (f : BoolDef)
    (h : ∀ l ∈ f.leaves, σ₁ l = σ₂ l) : f.evalB σ₁ = f.evalB σ₂ := by
  induction f with
  | lit l => exact h l (by simp [leaves])
  | and a b iha ihb =>
    simp only [evalB, iha fun l hl => h l (List.mem_append_left _ hl),
      ihb fun l hl => h l (List.mem_append_right _ hl)]
  | or a b iha ihb =>
    simp only [evalB, iha fun l hl => h l (List.mem_append_left _ hl),
      ihb fun l hl => h l (List.mem_append_right _ hl)]
  | neg a ih => simp only [evalB, ih h]
  | tru => rfl
  | fls => rfl

/-- Computable evaluation at the `decide` oracle agrees with the
propositional one. -/
theorem evalB_decide (τ : Literal → Prop) (f : BoolDef) :
    f.evalB (fun l => decide (τ l)) = decide (f.eval τ) := by
  induction f with
  | lit l => rfl
  | and a b iha ihb => simp [evalB, eval, iha, ihb]
  | or a b iha ihb => simp [evalB, eval, iha, ihb]
  | neg a ih => simp [evalB, eval, ih]
  | tru => simp [evalB, eval]
  | fls => simp [evalB, eval]

/-- All Boolean assignments over a literal list, as lookup lists. -/
def allAssign : List Literal → List (List (Literal × Bool))
  | [] => [[]]
  | l :: ls => (allAssign ls).flatMap fun σ => [(l, false) :: σ, (l, true) :: σ]

/-- Lookup in an assignment list (absent ↦ false — the engine only
ever queries leaves, which are present by construction). Recursive
(not `find?`) so the soundness lemmas rewrite by `simp [assignGet]`. -/
def assignGet : List (Literal × Bool) → Literal → Bool
  | [], _ => false
  | (l', v) :: σ, l => if decide (l' = l) then v else assignGet σ l

/-- The `decide`-canonical assignment is one of the enumerated ones. -/
theorem mem_allAssign (ls : List Literal) (τ : Literal → Prop) :
    (ls.map fun l => (l, decide (τ l))) ∈ allAssign ls := by
  classical
  induction ls with
  | nil => exact List.mem_singleton_self _
  | cons l ls ih =>
    simp only [allAssign, List.map_cons, List.mem_flatMap]
    exact ⟨_, ih, by cases h : decide (τ l) <;> simp⟩

/-- On a nodup literal list, the canonical assignment's lookup agrees
with `decide`. -/
theorem assignGet_map (ls : List Literal) (τ : Literal → Prop) (l : Literal)
    (hnd : ls.Nodup) (hl : l ∈ ls) :
    assignGet (ls.map fun l' => (l', decide (τ l'))) l = decide (τ l) := by
  classical
  induction ls with
  | nil => cases hl
  | cons l' ls ih =>
    obtain ⟨hd, ht⟩ := List.nodup_cons.mp hnd
    by_cases he : l' = l
    · subst he; simp [assignGet]
    · have htl : l ∈ ls := by
        cases hl with
        | head => exact absurd rfl he
        | tail _ h => exact h
      simp [assignGet, he, ih ht htl]

/-- Polarity normalization: `⟨b, true⟩` leaves become `.neg ⟨b, false⟩`.
The truth-table engine treats leaves as INDEPENDENT atoms — without
this, opposite-polarity literals of one bvar enumerate independently
and `l ∨ ¬l`-shaped forms (exactly what the Tseitin definitional
clauses become after inlining, nla-14 Slice 2) fail to check. -/
def normNeg : BoolDef → BoolDef
  | .lit l => if l.neg then .neg (.lit ⟨l.bvar, false⟩) else .lit l
  | .and a b => .and (normNeg a) (normNeg b)
  | .or a b => .or (normNeg a) (normNeg b)
  | .neg a => .neg (normNeg a)
  | .tru => .tru
  | .fls => .fls

/-- Normalization preserves evaluation under oracles consistent AT THE
FORM'S OWN LEAVES (per-leaf form: junk literals are NOT consistent —
`litHolds` poisons both polarities — so the quantifier must be
leaf-local). -/
theorem normNeg_correct (τ : Literal → Prop) :
    ∀ (f : BoolDef),
    (∀ l ∈ f.leaves, l.neg = true → (τ l ↔ ¬ τ ⟨l.bvar, false⟩)) →
    ((normNeg f).eval τ ↔ f.eval τ) := by
  intro f
  induction f with
  | lit l =>
    intro hτ
    cases hn : l.neg with
    | false =>
      have hl : l = ⟨l.bvar, false⟩ := by cases l; simp_all
      rw [hl]
      simp [normNeg, eval]
    | true =>
      have hl : l = Literal.negate ⟨l.bvar, false⟩ := by cases l; simp_all [Literal.negate]
      have ht := (hτ l (by simp [leaves]) hn).symm
      rw [hl] at ht ⊢
      simp only [normNeg, Literal.negate, Bool.not_false, eval, ite_true]
      -- goal: ¬ τ ⟨l.bvar, false⟩ ↔ τ (negate ⟨l.bvar, false⟩); ht matches
      -- up to the (kernel-computable) `!false` reduction
      exact ht
  | and a b iha ihb =>
    intro hτ
    exact and_congr (iha fun l hl => hτ l (List.mem_append_left _ hl))
      (ihb fun l hl => hτ l (List.mem_append_right _ hl))
  | or a b iha ihb =>
    intro hτ
    exact or_congr (iha fun l hl => hτ l (List.mem_append_left _ hl))
      (ihb fun l hl => hτ l (List.mem_append_right _ hl))
  | neg a ih =>
    intro hτ
    simp only [normNeg, eval]
    exact not_congr (ih hτ)
  | tru => intro _; exact Iff.rfl
  | fls => intro _; exact Iff.rfl

/-- Decidable tautology check: true iff every valuation of the
(dedup'd) leaves of the POLARITY-NORMALIZED form satisfies it. -/
def taut (f : BoolDef) : Bool :=
  (allAssign (normNeg f).leaves.dedup).all fun σ => (normNeg f).evalB (assignGet σ)

/-- Soundness of the tautology check: a `true` verdict reflects to
propositional validity of the NORMALIZED form under any oracle. -/
theorem taut_sound {f : BoolDef} (h : f.taut = true) (τ : Literal → Prop) :
    (normNeg f).eval τ := by
  classical
  have h' : (allAssign (normNeg f).leaves.dedup).all
      (fun σ => (normNeg f).evalB (assignGet σ)) = true := h
  have hmem := mem_allAssign (normNeg f).leaves.dedup τ
  have hb : (normNeg f).evalB
      (assignGet ((normNeg f).leaves.dedup.map fun l => (l, decide (τ l)))) = true :=
    List.all_eq_true.mp h' _ hmem
  have hget : ∀ l ∈ (normNeg f).leaves,
      assignGet ((normNeg f).leaves.dedup.map fun l' => (l', decide (τ l'))) l
        = decide (τ l) :=
    fun l hl => assignGet_map _ _ _ (List.nodup_dedup _) (List.mem_dedup.mpr hl)
  rw [evalB_ext (normNeg f) hget, evalB_decide] at hb
  exact of_decide_eq_true hb

/-- The use-site form: oracles consistent at the form's leaves get
validity of the ORIGINAL form. -/
theorem taut_sound_consistent {f : BoolDef} (h : f.taut = true) (τ : Literal → Prop)
    (hτ : ∀ l ∈ f.leaves, l.neg = true → (τ l ↔ ¬ τ ⟨l.bvar, false⟩)) : f.eval τ :=
  (normNeg_correct τ f hτ).mp (taut_sound h τ)

/-- Consequence check: every valuation satisfying `g` satisfies `f`
(the root-clause bridge shape — the clause follows from its source
hypothesis's form). -/
def conseq (g f : BoolDef) : Bool := taut (or (neg g) f)

theorem conseq_sound {g f : BoolDef} (h : conseq g f = true) (τ : Literal → Prop)
    (hτ : ∀ l ∈ (or (neg g) f).leaves, l.neg = true → (τ l ↔ ¬ τ ⟨l.bvar, false⟩))
    (hg : g.eval τ) : f.eval τ := by
  have h' := taut_sound_consistent h τ hτ
  simp only [eval] at h'
  rcases h' with hn | hf
  · exact absurd hg hn
  · exact hf

end BoolDef

/-- `litHolds` is polarity-consistent on DECODABLE literals (junk
poisons both polarities to `False` — the documented sound direction —
so the hypothesis is needed; the frontend's literals are all
registered/decodable). The `taut_sound_consistent` oracle hypothesis. -/
theorem litHolds_negate (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (l : Literal)
    (hdec : ∃ a, atoms[l.bvar]? = some (some a)) :
    litHolds ρ atoms l.negate ↔ ¬ litHolds ρ atoms l := by
  obtain ⟨a, ha⟩ := hdec
  obtain ⟨b, n⟩ := l
  have ha' : atoms[b]? = some (some a) := ha
  cases a with
  | ineq ia =>
    simp only [litHolds, ALitHolds, Literal.negate, ha']
    cases n <;> simp
  | root ra =>
    simp only [litHolds, ALitHolds, Literal.negate, ha']
    cases n <;> simp
  | bool d =>
    simp only [litHolds, Literal.negate, ha']
    cases n <;> simp

/-- A clause as a Boolean form: the right-associated disjunction of its
literals, `fls`-terminated. -/
def clauseForm : List Literal → BoolDef
  | [] => .fls
  | l :: C => .or (.lit l) (clauseForm C)

/-- The bridge the walk's bridges consume: `clauseHolds` IS the eval of
the clause's form under the literal semantics. (nla-14 Slice 2: the
Tseitin definitional-clause bridges are
`(clauseHolds_iff_eval …).mpr (taut_sound …)`; root units are direct
∃-introductions.) -/
theorem clauseHolds_iff_eval (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (C : List Literal) :
    clauseHolds ρ atoms C ↔ BoolDef.eval (litHolds ρ atoms) (clauseForm C) := by
  induction C with
  | nil =>
    simp only [clauseHolds, clauseForm, BoolDef.eval]
    constructor
    · intro h; obtain ⟨l, hl, _⟩ := h; cases hl
    · intro h; exact h.elim
  | cons l C ih =>
    simp only [clauseHolds, clauseForm, BoolDef.eval]
    constructor
    · rintro ⟨l', hl', h⟩
      rw [List.mem_cons] at hl'
      rcases hl' with rfl | hl'
      · exact Or.inl h
      · exact Or.inr (ih.mp ⟨l', hl', h⟩)
    · intro h
      rcases h with h | h
      · exact ⟨l, List.mem_cons_self, h⟩
      · obtain ⟨l', hl', h'⟩ := ih.mpr h
        exact ⟨l', List.mem_cons_of_mem _ hl', h'⟩

/-- Leaves of a clause's form are the clause's literals. -/
theorem mem_clauseForm_leaves (C : List Literal) (l : Literal) :
    l ∈ (clauseForm C).leaves ↔ l ∈ C := by
  induction C with
  | nil => simp [clauseForm, BoolDef.leaves]
  | cons x C ih =>
    simp [clauseForm, BoolDef.leaves, List.mem_cons, ih]

/-- The normalized-clause-form bridge: with decodability (the walk's
`precheck` guarantee for referenced inputs), `litHolds` is consistent
at the leaves, so `normNeg` is evaluation-invisible. -/
theorem clauseHolds_iff_evalNorm (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (C : List Literal) (hdec : clauseDecodable atoms C = true) :
    clauseHolds ρ atoms C ↔
    BoolDef.eval (litHolds ρ atoms) (BoolDef.normNeg (clauseForm C)) := by
  rw [clauseHolds_iff_eval]
  apply Iff.symm
  apply BoolDef.normNeg_correct
  intro l hl hn
  have hmem : l ∈ C := (mem_clauseForm_leaves C l).mp hl
  have hdecL := clauseDecodable_true atoms C hdec l hmem
  have hlit : l = ⟨l.bvar, true⟩ := by cases l; simp_all
  rw [hlit]
  exact litHolds_negate ρ atoms ⟨l.bvar, false⟩ hdecL


/-! ## One-step unfolding/bridge lemmas for the frontend (nla-14 Slice 2)

`boolDefHolds` is WF-compiled (fuel × structure measure), so the kernel
does NOT iota-reduce it — the Tseitin bridge construction is term-mode
and needs NAMED per-variant unfoldings (the `holds_single_*` idiom).
Fuel flow: `litHolds`/`interp` enter defs at fuel `atoms.size`; the
`.lit`-proxy step consumes one unit; conformant (acyclic, in-range)
tables never hit 0 on a real path (depth ≤ #proxies ≤ size). -/

theorem boolDefHolds_and (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (fuel : Nat)
    (a b : BoolDef) :
    boolDefHolds ρ atoms fuel (.and a b) ↔
    (boolDefHolds ρ atoms fuel a ∧ boolDefHolds ρ atoms fuel b) := by
  simp only [boolDefHolds]

theorem boolDefHolds_or (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (fuel : Nat)
    (a b : BoolDef) :
    boolDefHolds ρ atoms fuel (.or a b) ↔
    (boolDefHolds ρ atoms fuel a ∨ boolDefHolds ρ atoms fuel b) := by
  simp only [boolDefHolds]

theorem boolDefHolds_neg (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (fuel : Nat)
    (a : BoolDef) :
    boolDefHolds ρ atoms fuel (.neg a) ↔ ¬ boolDefHolds ρ atoms fuel a := by
  simp only [boolDefHolds]

theorem boolDefHolds_tru (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (fuel : Nat) :
    boolDefHolds ρ atoms fuel .tru ↔ True := by
  simp only [boolDefHolds]

theorem boolDefHolds_fls (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (fuel : Nat) :
    boolDefHolds ρ atoms fuel .fls ↔ False := by
  simp only [boolDefHolds]

/-- Literal-level unfolding at a proxy slot (the bound guard surfaced
as a `dite` — applies at any bound by kernel iota on the bound
numeral + the decidable `<`). -/
theorem boolDefHolds_lit_bool (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (l : Literal) (d : BoolDef) (bound : Nat)
    (h : atoms[l.bvar]? = some (some (.bool d))) :
    boolDefHolds ρ atoms bound (.lit l) ↔
    (if hb : l.bvar < bound then
       (if l.neg then ¬ boolDefHolds ρ atoms l.bvar d
        else boolDefHolds ρ atoms l.bvar d)
     else False) := by
  simp only [boolDefHolds, h]

/-- Literal-level unfolding at an ineq slot (fuel-free) — the bridge to
`litHolds` for arith leaves. -/
theorem boolDefHolds_lit_ineq (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (l : Literal) (a : IneqAtom) (fuel : Nat)
    (h : atoms[l.bvar]? = some (some (.ineq a))) :
    boolDefHolds ρ atoms fuel (.lit l) ↔ litHolds ρ atoms l := by
  simp only [boolDefHolds, litHolds, h]

/-- The root-atom counterpart. -/
theorem boolDefHolds_lit_root (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (l : Literal) (a : RootAtom) (fuel : Nat)
    (h : atoms[l.bvar]? = some (some (.root a))) :
    boolDefHolds ρ atoms fuel (.lit l) ↔ litHolds ρ atoms l := by
  simp only [boolDefHolds, litHolds, h]

/-- `litHolds` at a proxy slot unfolds to the def at fuel `atoms.size`. -/
theorem litHolds_bool (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (p : Nat) (neg : Bool) (d : BoolDef)
    (h : atoms[p]? = some (some (.bool d))) :
    litHolds ρ atoms ⟨p, neg⟩ ↔
    (if neg then ¬ boolDefHolds ρ atoms atoms.size d
     else boolDefHolds ρ atoms atoms.size d) := by
  simp only [litHolds, h]

/-- `interp` at a proxy slot, same shape. -/
theorem interp_bool (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (p : Nat) (d : BoolDef)
    (h : atoms[p]? = some (some (.bool d))) :
    interp ρ atoms p ↔ boolDefHolds ρ atoms atoms.size d := by
  simp only [interp, h]

/-- Every PROXY leaf of `d` (a leaf indexing a `.bool` slot) sits
strictly below `bound` (decide-grade). Arith/junk leaves pass. -/
def proxyLeavesLT (atoms : Array (Option Atom)) (bound : Nat) : BoolDef → Bool
  | .lit l =>
    match atoms[l.bvar]? with
    | some (some (.bool _)) => decide (l.bvar < bound)
    | _ => true
  | .and a b => proxyLeavesLT atoms bound a && proxyLeavesLT atoms bound b
  | .or a b => proxyLeavesLT atoms bound a && proxyLeavesLT atoms bound b
  | .neg a => proxyLeavesLT atoms bound a
  | .tru => true
  | .fls => true

/-- The Tseitin emission-order invariant, checked from index `b`:
every proxy's def has its proxy leaves strictly below the proxy's own
bvar (the frontend creates proxies bottom-up). Discharged by `decide`
on the concrete table. -/
def boolDefsOrderedFrom (atoms : Array (Option Atom)) (b : Nat) :
    List (Option Atom) → Bool
  | [] => true
  | a :: rest =>
    (match a with
     | some (.bool d) => proxyLeavesLT atoms b d
     | _ => true) && boolDefsOrderedFrom atoms (b + 1) rest

/-- The full-table check. -/
def boolDefsOrdered (atoms : Array (Option Atom)) : Bool :=
  boolDefsOrderedFrom atoms 0 atoms.toList

/-- Extraction: a `.bool` slot's def satisfies its leaf bound. -/
theorem boolDefsOrderedFrom_at (atoms : Array (Option Atom)) (l : List (Option Atom))
    (n i : Nat) (d : BoolDef)
    (h : boolDefsOrderedFrom atoms n l = true)
    (hl : l[i]? = some (some (.bool d))) :
    proxyLeavesLT atoms (n + i) d = true := by
  induction l generalizing n i with
  | nil => simp [List.getElem?_nil] at hl
  | cons a rest ih =>
    simp only [boolDefsOrderedFrom, Bool.and_eq_true] at h
    obtain ⟨ha, hr⟩ := h
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero] at hl
      injection hl with hl'
      subst hl'
      simpa using ha
    | succ j =>
      simp only [List.getElem?_cons_succ] at hl
      have := ih (n + 1) j hr hl
      rwa [show n + 1 + j = n + (j + 1) by omega] at this

/-- The table-level entry point. -/
theorem boolDefsOrdered_at (atoms : Array (Option Atom))
    (hord : boolDefsOrdered atoms = true) (p : Nat) (d : BoolDef)
    (hl : atoms[p]? = some (some (.bool d))) :
    proxyLeavesLT atoms p d = true := by
  have hl' : atoms.toList[p]? = some (some (.bool d)) := by
    rwa [← Array.getElem?_toList] at hl
  have := boolDefsOrderedFrom_at atoms atoms.toList 0 p d hord hl'
  simpa using this

/-- Path-independence: when both bounds cover `d`'s proxy leaves, the
bound is invisible (the `.lit`-proxy step recurses at the same child
bvar from both sides, so the two evaluations never diverge). -/
theorem boolDefHolds_irrel (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (hord : boolDefsOrdered atoms = true) :
    ∀ (b1 b2 : Nat) (d : BoolDef),
    proxyLeavesLT atoms b1 d = true → proxyLeavesLT atoms b2 d = true →
    (boolDefHolds ρ atoms b1 d ↔ boolDefHolds ρ atoms b2 d) := by
  intro b1 b2 d
  induction d with
  | lit l =>
    intro h1 h2
    cases hl : atoms[l.bvar]? with
    | none => simp only [boolDefHolds, hl]
    | some o =>
      cases o with
      | none => simp only [boolDefHolds, hl]
      | some a =>
        cases a with
        | ineq ia => simp only [boolDefHolds, hl]
        | root ra => simp only [boolDefHolds, hl]
        | bool d' =>
          simp only [proxyLeavesLT, hl] at h1 h2
          have hb1 := of_decide_eq_true h1
          have hb2 := of_decide_eq_true h2
          simp only [boolDefHolds, hl, dif_pos hb1, dif_pos hb2]
  | and a b iha ihb =>
    intro h1 h2
    simp only [proxyLeavesLT, Bool.and_eq_true] at h1 h2
    obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2
    simp only [boolDefHolds]
    exact and_congr (iha h1a h2a) (ihb h1b h2b)
  | or a b iha ihb =>
    intro h1 h2
    simp only [proxyLeavesLT, Bool.and_eq_true] at h1 h2
    obtain ⟨h1a, h1b⟩ := h1; obtain ⟨h2a, h2b⟩ := h2
    simp only [boolDefHolds]
    exact or_congr (iha h1a h2a) (ihb h1b h2b)
  | neg a ih =>
    intro h1 h2
    simp only [proxyLeavesLT] at h1 h2
    simp only [boolDefHolds]
    exact not_congr (ih h1 h2)
  | tru => intro _ _; simp only [boolDefHolds]
  | fls => intro _ _; simp only [boolDefHolds]

/-- Monotonicity of the leaf bound. -/
theorem proxyLeavesLT_mono (atoms : Array (Option Atom)) :
    ∀ (b b' : Nat) (d : BoolDef), proxyLeavesLT atoms b d = true → b ≤ b' →
    proxyLeavesLT atoms b' d = true := by
  intro b b' d
  induction d with
  | lit l =>
    intro h hbb
    cases hl : atoms[l.bvar]? with
    | none => simp only [proxyLeavesLT, hl]
    | some o =>
      cases o with
      | none => simp only [proxyLeavesLT, hl]
      | some a =>
        cases a with
        | ineq ia => simp only [proxyLeavesLT, hl]
        | root ra => simp only [proxyLeavesLT, hl]
        | bool d' =>
          simp only [proxyLeavesLT, hl, decide_eq_true_eq] at h ⊢
          exact lt_of_lt_of_le h hbb
  | and x y ihx ihy =>
    intro h hbb
    simp only [proxyLeavesLT, Bool.and_eq_true] at h ⊢
    obtain ⟨hx, hy⟩ := h
    exact ⟨ihx hx hbb, ihy hy hbb⟩
  | or x y ihx ihy =>
    intro h hbb
    simp only [proxyLeavesLT, Bool.and_eq_true] at h ⊢
    obtain ⟨hx, hy⟩ := h
    exact ⟨ihx hx hbb, ihy hy hbb⟩
  | neg x ih =>
    intro h hbb
    simp only [proxyLeavesLT] at h ⊢
    exact ih h hbb
  | tru => intro _ _; rfl
  | fls => intro _ _; rfl

/-- The boundary bridge: at a conformant (ordered) table, table
evaluation of a def at a covering bound IS the structural `eval` under
the literal semantics. This is what lets the frontend's per-proxy Iffs
compose WITHOUT unfolding shared defs (z3's Tseitin sharing survives
into the checked proof terms). -/
theorem boolDefHolds_evalLitHolds (ρ : Nat → ℝ) (atoms : Array (Option Atom))
    (hord : boolDefsOrdered atoms = true) :
    ∀ (bound : Nat) (d : BoolDef),
    proxyLeavesLT atoms bound d = true →
    (boolDefHolds ρ atoms bound d ↔ BoolDef.eval (litHolds ρ atoms) d) := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | _ bound ihB =>
    intro d
    induction d with
    | lit l =>
      intro hlt
      obtain ⟨lb, ln⟩ := l
      cases hl : atoms[lb]? with
      | none => simp [boolDefHolds, BoolDef.eval, litHolds, hl]
      | some o =>
        cases o with
        | none => simp [boolDefHolds, BoolDef.eval, litHolds, hl]
        | some a =>
          cases a with
          | ineq ia => simp [boolDefHolds, BoolDef.eval, litHolds, hl]
          | root ra => simp [boolDefHolds, BoolDef.eval, litHolds, hl]
          | bool d' =>
            simp only [proxyLeavesLT, hl] at hlt
            have hbb := of_decide_eq_true hlt
            have hltSize : lb < atoms.size := by
              have h' := Array.getElem?_eq_some_iff.mp hl
              exact h'.1
            have hordAt : proxyLeavesLT atoms lb d' = true :=
              boolDefsOrdered_at atoms hord lb d' hl
            have hSize : proxyLeavesLT atoms atoms.size d' = true :=
              proxyLeavesLT_mono atoms lb atoms.size d' hordAt (le_of_lt hltSize)
            have irS := boolDefHolds_irrel ρ atoms hord atoms.size lb d' hSize hordAt
            have step1 := boolDefHolds_lit_bool ρ atoms ⟨lb, ln⟩ d' bound hl
            rw [dif_pos hbb] at step1
            have step2 := litHolds_bool ρ atoms lb ln d' hl
            cases ln with
            | false =>
              show _ ↔ litHolds ρ atoms ⟨lb, false⟩
              have s1 : boolDefHolds ρ atoms bound (.lit ⟨lb, false⟩) ↔
                  boolDefHolds ρ atoms lb d' := by simpa using step1
              have s2 : litHolds ρ atoms ⟨lb, false⟩ ↔
                  boolDefHolds ρ atoms atoms.size d' := by
                simpa using step2
              exact s1.trans (s2.trans irS).symm
            | true =>
              show _ ↔ litHolds ρ atoms ⟨lb, true⟩
              have s1 : boolDefHolds ρ atoms bound (.lit ⟨lb, true⟩) ↔
                  ¬ boolDefHolds ρ atoms lb d' := by simpa using step1
              have s2 : litHolds ρ atoms ⟨lb, true⟩ ↔
                  ¬ boolDefHolds ρ atoms atoms.size d' := by
                simpa using step2
              exact s1.trans (s2.trans (not_congr irS)).symm
    | and a b iha ihb =>
      intro hlt
      simp only [proxyLeavesLT, Bool.and_eq_true] at hlt
      obtain ⟨ha, hb⟩ := hlt
      simp only [boolDefHolds, BoolDef.eval]
      exact and_congr (iha ha) (ihb hb)
    | or a b iha ihb =>
      intro hlt
      simp only [proxyLeavesLT, Bool.and_eq_true] at hlt
      obtain ⟨ha, hb⟩ := hlt
      simp only [boolDefHolds, BoolDef.eval]
      exact or_congr (iha ha) (ihb hb)
    | neg a ih =>
      intro hlt
      simp only [proxyLeavesLT] at hlt
      simp only [boolDefHolds, BoolDef.eval]
      exact not_congr (ih hlt)
    | tru => intro _; simp [boolDefHolds, BoolDef.eval]
    | fls => intro _; simp [boolDefHolds, BoolDef.eval]

/-! ## The unit-propagation engine (R1/F3) -//-! ## The unit-propagation engine (R1/F3) -//-! ## The unit-propagation engine (R1/F3) -//-! ## The unit-propagation engine (R1/F3) -//-! ## The unit-propagation engine (R1/F3) -/

/-- One literal's status under the partial assignment. -/
inductive LitStatus | sat | fals | un
deriving Repr, DecidableEq

def litStatus (σ : List (Option Bool)) (l : Literal) : LitStatus :=
  match σ[l.bvar]? with
  | some (some v) => if v == !l.neg then .sat else .fals
  | _ => .un

/-- One clause's status: `falsified` (every literal falsified),
`unit l` (`l` unassigned, every other literal falsified), or `other`
(satisfied, or ≥ 2 unassigned literals). Structural over the literal
list so the connective lemmas are plain inductions. -/
inductive ClauseStatus | falsified | unit (l : Literal) | other
deriving Repr

def clauseStatus (σ : List (Option Bool)) : List Literal → ClauseStatus
  | [] => .falsified
  | l :: ls =>
    match litStatus σ l with
    | .sat => .other
    | .fals => clauseStatus σ ls
    | .un =>
      match clauseStatus σ ls with
      | .falsified => .unit l
      | _ => .other

/-- The scan result: the first falsified or unit clause, with the
clause carried for the soundness proof's membership facts. -/
inductive ScanResult
  | conflict (C : List Literal)
  | unit (C : List Literal) (l : Literal)
  | fixpoint

def scan (σ : List (Option Bool)) : List (List Literal) → ScanResult
  | [] => .fixpoint
  | C :: Cs =>
    match clauseStatus σ C with
    | .falsified => .conflict C
    | .unit l => .unit C l
    | .other => scan σ Cs

/-- The propagation loop. Fuel only bounds completeness (junk/
out-of-range assignments can't loop forever); every `true` comes from
a real conflict — that is all the soundness proof uses. -/
def upLoop (F : List (List Literal)) (σ : List (Option Bool)) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    match scan σ F with
    | .conflict _ => true
    | .fixpoint => false
    | .unit _ l => upLoop F (σ.set l.bvar (some (!l.neg))) fuel

/-- Install units. `none` = contradictory units (the unit list assigns
one bvar both values). Out-of-range bvars are dropped (dead defense —
`upRefutes`' size computation covers every bvar in `F`/`target`). -/
def applyUnits (σ : List (Option Bool)) : List Literal → Option (List (Option Bool))
  | [] => some σ
  | u :: us =>
    match σ[u.bvar]? with
    | some (some v') => if v' == !u.neg then applyUnits σ us else none
    | some none => applyUnits (σ.set u.bvar (some (!u.neg))) us
    | none => applyUnits σ us

/-- The RUP check: negate `target` into units, propagate, conflict? -/
def upRefutes (F : List (List Literal)) (target : List Literal) : Bool :=
  let sz := (F.foldl (fun m C => C.foldl (fun m l => max m (l.bvar + 1)) m)
    (target.foldl (fun m l => max m (l.bvar + 1)) 0))
  match applyUnits (List.replicate sz none) (target.map Literal.negate) with
  | none => true
  | some σ => upLoop F σ (sz + 1)

/-! ### Soundness -/

/-- Every assignment in `σ` is forced by the interpretation. -/
def forced (I : Nat → Prop) (σ : List (Option Bool)) : Prop :=
  ∀ b v, σ[b]? = some (some v) → litSatI I ⟨b, !v⟩

theorem litSatI_negate (I : Nat → Prop) (l : Literal) :
    litSatI I l.negate ↔ ¬ litSatI I l := by
  obtain ⟨b, n⟩ := l
  cases n <;> simp [litSatI, Literal.negate]

/-- A falsified literal does not hold (given forcedness). -/
theorem not_litSatI_of_fals (hforced : forced I σ) (l : Literal)
    (h : litStatus σ l = .fals) : ¬ litSatI I l := by
  obtain ⟨b, n⟩ := l
  unfold litStatus at h
  split at h
  · rename_i v hv
    by_cases hv' : v = !n
    · simp [hv'] at h
    · have hf := hforced b v hv
      have hv'' : v = n := by cases v <;> cases n <;> simp_all
      rw [hv''] at hf
      exact (litSatI_negate I ⟨b, n⟩).mp hf
  · simp at h

theorem clauseStatus_falsified (σ : List (Option Bool)) (C : List Literal) :
    clauseStatus σ C = .falsified → ∀ l ∈ C, litStatus σ l = .fals := by
  induction C with
  | nil => intro _ l hl; cases hl
  | cons l ls ih =>
    intro h l' hl'
    unfold clauseStatus at h
    split at h
    · simp at h
    · rename_i hl
      cases hl' with
      | head => exact hl
      | tail _ hm => exact ih h l' hm
    · revert h
      split <;> intro h <;> simp at h

theorem clauseStatus_unit (σ : List (Option Bool)) (C : List Literal) (l : Literal) :
    clauseStatus σ C = .unit l →
    l ∈ C ∧ litStatus σ l = .un ∧ ∀ l' ∈ C, l' ≠ l → litStatus σ l' = .fals := by
  induction C with
  | nil => intro h; simp [clauseStatus] at h
  | cons l₀ ls ih =>
    intro h
    unfold clauseStatus at h
    split at h
    · simp at h
    · rename_i hl₀
      obtain ⟨hmem, hun, hrest⟩ := ih h
      refine ⟨List.mem_cons_of_mem _ hmem, hun, ?_⟩
      intro l' hl' hne
      cases hl' with
      | head => exact hl₀
      | tail _ hm => exact hrest l' hm hne
    · rename_i hl₀
      split at h
      · rename_i htail
        simp at h
        obtain rfl := h
        refine ⟨.head _, hl₀, ?_⟩
        intro l' hl' hne
        cases hl' with
        | head => exact absurd rfl hne
        | tail _ hm => exact clauseStatus_falsified σ ls htail l' hm
      · simp at h

theorem scan_conflict (σ : List (Option Bool)) (F : List (List Literal))
    (C : List Literal) :
    scan σ F = .conflict C → C ∈ F ∧ clauseStatus σ C = .falsified := by
  induction F with
  | nil => intro h; simp [scan] at h
  | cons C₀ Cs ih =>
    intro h
    unfold scan at h
    split at h
    · rename_i hs
      simp at h
      obtain rfl := h
      exact ⟨.head _, hs⟩
    · simp at h
    · obtain ⟨hm, hs⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hs⟩

theorem scan_unit (σ : List (Option Bool)) (F : List (List Literal))
    (C : List Literal) (l : Literal) :
    scan σ F = .unit C l → C ∈ F ∧ clauseStatus σ C = .unit l := by
  induction F with
  | nil => intro h; simp [scan] at h
  | cons C₀ Cs ih =>
    intro h
    unfold scan at h
    split at h
    · simp at h
    · rename_i l' hs
      simp at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨.head _, hs⟩
    · obtain ⟨hm, hs⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hm, hs⟩

/-- Propagation preserves forcedness: the newly assigned literal is the
unit clause's only unfalsified literal, so it must hold. -/
theorem forced_set_of_unit (I : Nat → Prop) (F : List (List Literal))
    (hF : ∀ C ∈ F, clauseSatI I C) (σ : List (Option Bool))
    (hforced : forced I σ) (C : List Literal) (l : Literal)
    (hC : C ∈ F) (h : clauseStatus σ C = .unit l) :
    forced I (σ.set l.bvar (some (!l.neg))) := by
  obtain ⟨hlC, hun, hrest⟩ := clauseStatus_unit σ C l h
  have hl : litSatI I l := by
    obtain ⟨l₀, hl₀C, hl₀⟩ := hF C hC
    by_cases he : l₀ = l
    · subst he; exact hl₀
    · exact absurd hl₀ (not_litSatI_of_fals hforced l₀ (hrest l₀ hl₀C he))
  intro b v hbv
  rw [List.getElem?_set] at hbv
  split at hbv
  · rename_i hb
    split at hbv
    · simp only [Option.some.injEq] at hbv
      subst hb
      obtain rfl := hbv
      rw [Bool.not_not]
      exact hl
    · simp at hbv
  · exact hforced b v hbv

/-- The loop only returns `true` on a genuine conflict. -/
theorem upLoop_sound (I : Nat → Prop) (F : List (List Literal))
    (hF : ∀ C ∈ F, clauseSatI I C) :
    ∀ (σ : List (Option Bool)) (fuel : Nat),
      forced I σ → upLoop F σ fuel = true → False := by
  intro σ fuel
  induction fuel generalizing σ with
  | zero => intro _ h; simp [upLoop] at h
  | succ fuel ih =>
    intro hforced h
    unfold upLoop at h
    split at h
    · rename_i C hs
      obtain ⟨hC, hstat⟩ := scan_conflict σ F C hs
      obtain ⟨l, hlC, hl⟩ := hF C hC
      exact not_litSatI_of_fals hforced l (clauseStatus_falsified σ C hstat l hlC) hl
    · simp at h
    · rename_i C l hs
      obtain ⟨hC, hstat⟩ := scan_unit σ F C l hs
      exact ih _ (forced_set_of_unit I F hF σ hforced C l hC hstat) h

/-- Installing units: the some-case extends forcedness, the none-case
is already contradictory (a bvar forced both ways). -/
theorem applyUnits_sound (I : Nat → Prop) (us : List Literal) :
    (∀ u ∈ us, litSatI I u) →
    ∀ (σ : List (Option Bool)), forced I σ →
      (∀ σ', applyUnits σ us = some σ' → forced I σ') ∧
      (applyUnits σ us = none → False) := by
  induction us with
  | nil =>
    intro _ σ hforced
    refine ⟨fun σ' h => ?_, fun h => by simp [applyUnits] at h⟩
    simp [applyUnits] at h
    subst h
    exact hforced
  | cons u us ih =>
    intro hus σ hforced
    unfold applyUnits
    split
    · rename_i v' hv
      split
      · exact ih (fun u' hu' => hus u' (List.mem_cons_of_mem _ hu')) σ hforced
      · rename_i hs
        refine ⟨fun σ' h' => by simp at h', fun _ => ?_⟩
        have hf := hforced u.bvar v' hv
        have hu : litSatI I u := hus u (.head _)
        have hvv : v' = u.neg := by
          cases v' <;> cases hu' : u.neg <;> simp_all
        rw [hvv] at hf
        exact (litSatI_negate I u).mp hf hu
    · rename_i hv
      have hu : litSatI I u := hus u (.head _)
      have hnew : forced I (σ.set u.bvar (some (!u.neg))) := by
        intro b v hbv
        rw [List.getElem?_set] at hbv
        split at hbv
        · rename_i hb
          split at hbv
          · simp only [Option.some.injEq] at hbv
            subst hb
            obtain rfl := hbv
            rw [Bool.not_not]
            exact hu
          · simp at hbv
        · exact hforced b v hbv
      exact ih (fun u' hu' => hus u' (List.mem_cons_of_mem _ hu')) _ hnew
    · exact ih (fun u' hu' => hus u' (List.mem_cons_of_mem _ hu')) σ hforced

theorem forced_replicate (I : Nat → Prop) (sz : Nat) :
    forced I (List.replicate sz none) := by
  intro b v hbv
  rw [List.getElem?_replicate] at hbv
  split at hbv <;> simp at hbv

theorem upRefutes_go_sound (I : Nat → Prop) (F : List (List Literal))
    (hF : ∀ C ∈ F, clauseSatI I C)
    (units : List Literal) (hus : ∀ u ∈ units, litSatI I u)
    (σ₀ : List (Option Bool)) (hforced₀ : forced I σ₀) (fuel : Nat) :
    (match applyUnits σ₀ units with
     | none => true
     | some σ => upLoop F σ fuel) = true → False := by
  intro h
  split at h
  · rename_i hAp
    exact (applyUnits_sound I units hus σ₀ hforced₀).2 hAp
  · rename_i σ hAp
    have hforced := (applyUnits_sound I units hus σ₀ hforced₀).1 σ hAp
    exact upLoop_sound I F hF σ _ hforced h

/-- **RUP soundness**: if the checker finds a conflict, the clause set
`F` plus the negated target is unsatisfiable — i.e. `target` follows
from `F`. -/
theorem upRefutes_sound (I : Nat → Prop) (F : List (List Literal))
    (target : List Literal) (hF : ∀ C ∈ F, clauseSatI I C)
    (ht : ∀ l ∈ target, ¬ litSatI I l) :
    upRefutes F target = true → False := by
  intro h
  have hunits : ∀ u ∈ target.map Literal.negate, litSatI I u := by
    intro u hu
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hu
    exact (litSatI_negate I l).mpr (ht l hl)
  exact upRefutes_go_sound I F hF _ hunits _ (forced_replicate I _) _ h

end LeanNonlinearArith.Nlsat
