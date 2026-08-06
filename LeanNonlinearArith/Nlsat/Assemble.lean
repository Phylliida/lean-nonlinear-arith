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
   only make `clauseHolds` harder to establish).

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

/-- The atom-table interpretation: bvar `b` holds iff the table maps it
to an atom that holds at `ρ`. Undecodable ↦ `False` (sound direction). -/
def interp (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (b : Nat) : Prop :=
  match atoms[b]? with
  | some (some a) => Atom.Holds ρ a
  | _ => False

/-- Solver-level literal semantics (the F2 extraction's form). -/
def litHolds (ρ : Nat → ℝ) (atoms : Array (Option Atom)) (l : Literal) : Prop :=
  match atoms[l.bvar]? with
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
  cases n <;> simp [litSatI, litHolds, interp, ALitHolds, ha]

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

/-! ## The unit-propagation engine (R1/F3) -/

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
