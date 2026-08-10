import LeanNonlinearArith.Nlsat.Refute
import LeanNonlinearArith.Nlsat.Trace

/-!
# nla-19a Slice F3 — the propositional DAG walk (`nlsat_refute`)

The last assembly layer of the 12d.6b⇄19a arc (design review 4,
R-iv/R-v/R-vi; review 5 re-scope): walk the solver's refutation DAG
from the `s.refutation` snapshot, establishing each learned clause from
its antecedents + arith lemmas via the verified RUP engine
(`upRefutes_sound`, Assemble.lean), closing `False` at the final
bundle's empty lemma.

**Input contract (R-vi):** the goal is

    ∀ ρ : Nat → ℝ, (∀ C ∈ Cs, clauseHolds ρ atoms C) → False

where `atoms` is the INTERNAL-order atom-table snapshot and `Cs` is
EXACTLY the referenced input clauses' literal lists in increasing cid
order. The tactic argument is the `s.refutation` payload
`(atoms, clauses, traceBundles, finalBundle)`.

**Native pre-checks are compiled, not interpreted.** Probe
(2026-08-09): `Meta.evalExpr` of a bare FUNCTION const
(`mkConst ``TraceBundle.isV0`) mis-evaluates on this toolchain —
`TraceBundle.isV0 b6` came back `false` where `#eval` gives `true`;
full APPLICATION exprs evaluate correctly. So all native checks live in
`precheck`, ordinary compiled code consumed by a single `evalExpr` of
its application. (Recorded on the board; root cause open.)

**Per learned cid** (increasing order — antecedent cids are always
smaller by creation order): the F-set is the bundle's antecedent
clauses (input → the bridged hypothesis, learned → the earlier fold
result) plus one `arithClause core proj` per `.arith` marker
(discharged by F2's `Refute.proveClauseSat`). `.decision` markers stay
in the lemma (skipped); non-resolution steps contribute no clause-level
facts at this layer (review 5, F-i). The learned clause follows by
`upRefutes_sound` with the RUP check discharged by `decide` (NEVER
`native_decide` in the trusted layer; per-bundle-local kernel cost,
R-v; the values are Nat/Bool only so kernel reduction is safe). The
final bundle's empty lemma yields `False` directly.

**Trust shape (R-viii):** untrusted meta producing kernel-checked
terms; every failure — precheck rejection, failed arith discharge,
kernel `decide` failure — is a tactic error = sound rejection.
-/

namespace LeanNonlinearArith.Nlsat

open Check
open Lean Meta Elab Tactic

namespace Walk

/-- The `s.refutation` payload type (atom table, clause table,
per-clause bundle table, final bundle). -/
abbrev SnapshotTy :=
  Array (Option Atom) × Array Clause × Array (Option TraceBundle) × TraceBundle

/-- Structural equality on literal lists — native pre-checks only (the
kernel re-verifies everything through the produced terms). -/
def litsEq : List Literal → List Literal → Bool
  | [], [] => true
  | l :: ls, l' :: ls' => l == l' && litsEq ls ls'
  | _, _ => false

/-- The native value of `arithClause core proj` (def-mirroring data
manipulation: `proj ++ core.map Literal.negate`). -/
def arithClauseVal (core proj : Array Literal) : List Literal :=
  proj.toList ++ core.toList.map Literal.negate

/-- The F-set clause VALUES of one bundle, computed from the snapshot
(learned antecedents resolve to the bundle lemmas — V1-pinned equal to
the clause table; input antecedents to the clause table). Errors:
out-of-range antecedent, forward reference, non-v0 step. -/
def nodeFSet (clauses : Array Clause) (bundles : Array (Option TraceBundle))
    (learnedLemmas : Array (Nat × List Literal)) (b : TraceBundle) :
    Except String (List (List Literal)) := do
  let mut F : List (List Literal) := []
  for step in b.steps do
    match step with
    | .resolution (.clause cid') =>
      if cid' < bundles.size then
        if bundles[cid']!.isSome then
          match learnedLemmas.find? (·.1 == cid') with
          | some (_, lem) => F := F ++ [lem]
          | none => throw s!"forward reference to learned clause {cid'}"
        else
          F := F ++ [clauses[cid']!.lits.toList]
      else throw s!"antecedent cid {cid'} out of range"
    | .resolution (.arith core proj) =>
      F := F ++ [arithClauseVal core proj]
    | .resolution (.decision _) => pure ()
    | .pseudoDivision .. | .intBranch .. => throw "non-v0 step"
    | _ => pure ()
  return F

/-- All native walk pre-checks in one compiled function (see the module
doc for why this is not interpreter-evaluated pieces): sizes, per-bundle
v0 gate, V1 lemma/ clause-table agreement, per-node RUP (the same
`upRefutes` the kernel later re-checks by `decide`), the final bundle's
empty lemma, the input-clause contract (referenced inputs in cid order
= the goal's `Cs`), atom-table agreement with the goal, and referenced
input decodability. -/
def precheck (snap : SnapshotTy) (goalAtoms : Array (Option Atom))
    (goalInputs : List (List Literal)) : Except String Unit := do
  let (atoms, clauses, bundles, final) := snap
  if atoms != goalAtoms then
    throw "atom table mismatch (goal vs snapshot)"
  if bundles.size != clauses.size then
    throw s!"traceBundles/clauses size mismatch ({bundles.size} vs {clauses.size})"
  let mut learnedLemmas : Array (Nat × List Literal) := #[]
  for cid in [0:clauses.size] do
    if let some b := bundles[cid]! then
      if !b.isV0 then throw s!"learned clause {cid}: bundle not v0-checkable"
      let F ← nodeFSet clauses bundles learnedLemmas b
      if !litsEq b.lemma.toList clauses[cid]!.lits.toList then
        throw s!"learned clause {cid}: bundle lemma ≠ clause table"
      if !upRefutes (F.map (·.dedup)) b.lemma.toList.dedup then
        throw s!"learned clause {cid}: RUP check failed"
      learnedLemmas := learnedLemmas.push (cid, b.lemma.toList)
  if !final.lemma.isEmpty then throw "final bundle's lemma is not empty"
  if !final.isV0 then throw "final bundle not v0-checkable"
  let Ff ← nodeFSet clauses bundles learnedLemmas final
  if !upRefutes (Ff.map (·.dedup)) [] then throw "final bundle: RUP check failed"
  -- input-clause contract: referenced input cids, increasing order
  let mut refSet : Array Nat := #[]
  for cid in [0:clauses.size] do
    if let some b := bundles[cid]! then
      for step in b.steps do
        if let .resolution (.clause cid') := step then
          if cid' < bundles.size && bundles[cid']!.isNone && !refSet.contains cid' then
            refSet := refSet.push cid'
  for step in final.steps do
    if let .resolution (.clause cid') := step then
      if cid' < bundles.size && bundles[cid']!.isNone && !refSet.contains cid' then
        refSet := refSet.push cid'
  let refSorted := refSet.qsort (· < ·)
  let expected := refSorted.toList.map fun cid => clauses[cid]!.lits.toList
  if !(expected.length == goalInputs.length &&
      (expected.zip goalInputs).all fun (a, b) => litsEq a b) then
    throw "input clause list mismatch (expected the referenced input \
      clauses in increasing cid order)"
  for cid in refSorted do
    for l in clauses[cid]!.lits do
      match atoms[l.bvar]? with
      | some (some _) => pure ()
      | _ => throw s!"input clause {cid}: undecodable literal {repr l}"

/-- The `List Literal` type expression. -/
def listLiteralE : Expr := mkApp (mkConst ``List [levelZero]) (mkConst ``Literal)

/-- Quote a literal list (cons-chains of `Literal.mk`; defeq to the
elaborated spelling). -/
def quoteLits (lits : List Literal) : MetaM Expr :=
  mkListLit (mkConst ``Literal) (lits.map Refute.litToExpr)

/-- Quote a list of clauses. -/
def quoteLitsList (cs : List (List Literal)) : MetaM Expr := do
  mkListLit listLiteralE (← cs.mapM quoteLits)

/-- Build `∀ C ∈ F, clauseSatI IE C` from per-clause proofs, via
`List.forall_mem_cons` folds with all implicits pinned (no HOU). -/
partial def forallMemFold (motiveE : Expr) :
    List (List Literal × Expr) → MetaM Expr
  | [] =>
    mkAppOptM ``List.forall_mem_nil #[some listLiteralE, some motiveE]
  | (Cval, pf) :: rest => do
    let restE ← forallMemFold motiveE rest
    let CE ← quoteLits Cval
    let restValE ← quoteLitsList (rest.map Prod.fst)
    let iffE ← mkAppOptM ``List.forall_mem_cons
      #[some listLiteralE, some motiveE, some CE, some restValE]
    let andE ← mkAppM ``And.intro #[pf, restE]
    mkAppM ``Iff.mpr #[iffE, andE]

/-- Membership proof of `CE` at position `i` of the concrete clause list
`tail`, via the `List.mem_cons` Iff chain with pinned implicits.
(`List.mem_cons` binder order: `{α} {b} {l} {a}` — probed 2026-08-09.) -/
partial def memChain : (tail : List (List Literal)) → Nat → Expr → MetaM Expr
  | head :: rest, 0, CE => do
    let headE ← quoteLits head
    let restE ← quoteLitsList rest
    let iffE ← mkAppOptM ``List.mem_cons
      #[some listLiteralE, some headE, some restE, some CE]
    let eqE := mkApp3 (mkConst ``Eq [levelOne]) listLiteralE CE headE
    let memRestE ← mkAppM ``Membership.mem #[restE, CE]
    let rflE ← mkEqRefl CE
    let orE ← mkAppOptM ``Or.inl #[some eqE, some memRestE, some rflE]
    mkAppM ``Iff.mpr #[iffE, orE]
  | head :: rest, i + 1, CE => do
    let recE ← memChain rest i CE
    let headE ← quoteLits head
    let restE ← quoteLitsList rest
    let iffE ← mkAppOptM ``List.mem_cons
      #[some listLiteralE, some headE, some restE, some CE]
    let eqE := mkApp3 (mkConst ``Eq [levelOne]) listLiteralE CE headE
    let memRestE ← mkAppM ``Membership.mem #[restE, CE]
    let orE ← mkAppOptM ``Or.inr #[some eqE, some memRestE, some recE]
    mkAppM ``Iff.mpr #[iffE, orE]
  | [], _, _ => throwError "nlsat_refute: memChain out of range"

/-- The F-set of a bundle as (values × `clauseSatI IE` proofs), in step
order. `.arith` markers are discharged by F2's `proveClauseSat` in a
sandboxed sub-goal; projection steps contribute no clause-level facts
(review 5, F-i). All malformed cases were already rejected by
`precheck` — the remaining `throwError`s are dead-code defense. -/
unsafe def buildFSet (IE : Expr)
    (inputFacts learnedFacts : Array (Nat × List Literal × Expr))
    (b : TraceBundle) (bundlesV : Array (Option TraceBundle)) :
    TacticM (List (List Literal) × List Expr) := do
  let mut Fvals : List (List Literal) := []
  let mut Fproofs : List Expr := []
  for step in b.steps do
    match step with
    | .resolution (.clause cid') =>
      if cid' < bundlesV.size then
        if bundlesV[cid']!.isSome then
          match learnedFacts.find? (fun (c, _, _) => c == cid') with
          | some (_, val, pf) =>
            Fvals := Fvals ++ [val]; Fproofs := Fproofs ++ [pf]
          | none => throwError "nlsat_refute: forward reference to learned clause {cid'}"
        else
          match inputFacts.find? (fun (c, _, _) => c == cid') with
          | some (_, val, pf) =>
            Fvals := Fvals ++ [val]; Fproofs := Fproofs ++ [pf]
          | none => throwError "nlsat_refute: antecedent {cid'} is not a referenced input clause"
      else throwError "nlsat_refute: antecedent cid {cid'} out of range"
    | .resolution (.arith core proj) =>
      let Cval := arithClauseVal core proj
      let CE ← quoteLits Cval
      let ty := mkApp2 (mkConst ``clauseSatI) IE CE
      let am ← mkFreshExprMVar ty
      let saved ← getGoals
      setGoals [am.mvarId!]
      try
        Refute.proveClauseSat am.mvarId!
      catch e =>
        setGoals saved
        throwError "nlsat_refute: arith lemma {repr Cval} failed to discharge: {e.toMessageData}"
      setGoals saved
      let pf ← instantiateMVars am
      Fvals := Fvals ++ [Cval]; Fproofs := Fproofs ++ [pf]
    | _ => pure ()
  return (Fvals, Fproofs)

/-- The RUP assembly for one node: kernel `decide` + `upRefutes_sound`,
returning the learned-clause proof (`byContradiction` shape).

R2' hardening (review 14): the decide computation runs on DEDUP'd
clauses — `clauseStatus` reads `[l, l]`-unassigned as `.other` (not
unit), stalling propagation on duplicate-literal learned clauses
(possible in z3: `processAntecedent` has no dedup in the mark path).
Semantic identity via `clauseSatI_dedup`/`not_litSatI_forall_dedup`;
the RETURNED proof is for the ORIGINAL clause list. -/
def rupNode (IE motiveE : Expr)
    (Fvals : List (List Literal)) (Fproofs : List Expr)
    (targetVal : List Literal) : MetaM Expr := do
  let FvalsD := Fvals.map (·.dedup)
  let targetValD := targetVal.dedup
  let targetE ← quoteLits targetValD
  let FE ← quoteLitsList FvalsD
  let hrup ← mkDecideProof
    (← mkAppM ``Eq #[mkApp2 (mkConst ``upRefutes) FE targetE, mkConst ``true])
  -- hF's antecedents are dedup'd clauses; bridge each proof
  let FproofsD ← (Fvals.zip Fproofs).mapM fun (C, pf) => do
    let CE ← quoteLits C
    mkAppM ``Iff.mpr #[(← mkAppM ``clauseSatI_dedup #[IE, CE]), pf]
  let hF ← forallMemFold motiveE (FvalsD.zip FproofsD)
  -- the returned fact is about the ORIGINAL clause list
  let targetOrigE ← quoteLits targetVal
  let targetPropE := mkApp2 (mkConst ``clauseSatI) IE targetOrigE
  let lamE ← withLocalDecl `hCon BinderInfo.default (mkApp (mkConst ``Not) targetPropE)
    fun hConE => do
      -- `mkAppM`, not `mkApp`: the head has leading implicits {I} {C}
      let htE ← mkAppM ``not_litSatI_forall_of_not_clauseSatI #[hConE]
      let htD ← mkAppM ``not_litSatI_forall_dedup #[IE, targetOrigE, htE]
      let upE := mkAppN (mkConst ``upRefutes_sound) #[IE, FE, targetE, hF, htD, hrup]
      -- `Classical.byContradiction : (¬p → False) → p` (4.25 core)
      mkLambdaFVars #[hConE] upE
  mkAppM ``Classical.byContradiction #[lamE]

/-- The walk. `mvar`'s goal: `∀ ρ, (∀ C ∈ Cs, clauseHolds ρ atoms C) →
False` with concrete `atoms`/`Cs`; `snapE` is the `s.refutation`
payload. -/
unsafe def walkRefutation (mvar : MVarId) (snapE : Expr) : TacticM Unit := do
  let snapTyE ← Term.elabType (← `(SnapshotTy))
  let (_, clausesV, bundlesV, finalV) ← Meta.evalExpr SnapshotTy snapTyE snapE
  let (ρFv, m1) ← mvar.intro `ρ
  let (hCFv, m2) ← m1.intro `hC
  m2.withContext do
    let ρE := mkFVar ρFv
    let hCE := mkFVar hCFv
    -- Extract `atomsE`/`CsE` from hC's type `∀ C ∈ Cs, clauseHolds ρ atoms C`.
    let hTy ← inferType hCE
    let (atomsE, CsE) ← match hTy with
      | .forallE _ _ (.forallE _ memTy body _) _ =>
        let (memFn, memArgs) := memTy.getAppFnArgs
        let (chFn, chArgs) := body.getAppFnArgs
        unless memFn == ``Membership.mem && chFn == ``clauseHolds && chArgs.size == 3 do
          throwError "nlsat_refute: hypothesis is not `∀ C ∈ Cs, clauseHolds ρ atoms C`"
        unless memArgs.size ≥ 2 do
          throwError "nlsat_refute: malformed membership hypothesis"
        pure (chArgs[1]!, memArgs[memArgs.size - 2]!)
      | _ =>
        throwError "nlsat_refute: hypothesis is not `∀ C ∈ Cs, clauseHolds ρ atoms C`"
    let CsV ← Meta.evalExpr (List (List Literal))
      (← Term.elabType (← `(List (List Literal)))) CsE
    let atomsV ← Meta.evalExpr (Array (Option Atom))
      (← Term.elabType (← `(Array (Option Atom)))) atomsE
    -- Native pre-checks (one compiled application — see module doc).
    let preTyE ← Term.elabType (← `(Except String Unit))
    let pre ← Meta.evalExpr (Except String Unit) preTyE
      (mkAppN (mkConst ``Walk.precheck) #[snapE, atomsE, CsE])
    if let .error e := pre then throwError "nlsat_refute: {e}"
    let IE := mkApp2 (mkConst ``interp) ρE atomsE
    let motiveE := mkApp (mkConst ``clauseSatI) IE
    -- Referenced input cids (precheck-verified to match CsV in order).
    let mut refSet : Array Nat := #[]
    for cid in [0:clausesV.size] do
      if let some b := bundlesV[cid]! then
        for step in b.steps do
          if let .resolution (.clause cid') := step then
            if cid' < bundlesV.size && bundlesV[cid']!.isNone && !refSet.contains cid' then
              refSet := refSet.push cid'
    for step in finalV.steps do
      if let .resolution (.clause cid') := step then
        if cid' < bundlesV.size && bundlesV[cid']!.isNone && !refSet.contains cid' then
          refSet := refSet.push cid'
    let refSorted := refSet.qsort (· < ·)
    -- Input facts: hypothesis → clauseHolds → (bridge) clauseSatI.
    let mut inputFacts : Array (Nat × List Literal × Expr) := #[]
    for i in [0:refSorted.size] do
      let cid := refSorted[i]!
      let Cval := clausesV[cid]!.lits.toList
      let CE ← quoteLits Cval
      let decPrf ← mkDecideProof (← mkAppM ``Eq
        #[mkApp2 (mkConst ``clauseDecodable) atomsE CE, mkConst ``true])
      let hdec := mkAppN (mkConst ``clauseDecodable_true) #[atomsE, CE, decPrf]
      let memE ← memChain CsV i CE
      let hHolds := mkAppN hCE #[CE, memE]
      let hSat ← mkAppM ``Iff.mpr
        #[mkAppN (mkConst ``clauseSatI_interp) #[ρE, atomsE, CE, hdec], hHolds]
      inputFacts := inputFacts.push (cid, Cval, hSat)
    -- Learned clauses in increasing cid order.
    let mut learnedFacts : Array (Nat × List Literal × Expr) := #[]
    for cid in [0:clausesV.size] do
      if let some b := bundlesV[cid]! then
        let (Fvals, Fproofs) ← buildFSet IE inputFacts learnedFacts b bundlesV
        let pf ← rupNode IE motiveE Fvals Fproofs b.lemma.toList
        learnedFacts := learnedFacts.push (cid, b.lemma.toList, pf)
    -- Final bundle: target [] ⇒ False. (Same R2' dedup as rupNode;
    -- the [] target is unaffected but the F-set clauses may carry
    -- duplicate literals.)
    let (Fvals, Fproofs) ← buildFSet IE inputFacts learnedFacts finalV bundlesV
    let FvalsD := Fvals.map (·.dedup)
    let targetE ← quoteLits []
    let FE ← quoteLitsList FvalsD
    let hrup ← mkDecideProof
      (← mkAppM ``Eq #[mkApp2 (mkConst ``upRefutes) FE targetE, mkConst ``true])
    let FproofsD ← (Fvals.zip Fproofs).mapM fun (C, pf) => do
      let CE ← quoteLits C
      mkAppM ``Iff.mpr #[(← mkAppM ``clauseSatI_dedup #[IE, CE]), pf]
    let hF ← forallMemFold motiveE (FvalsD.zip FproofsD)
    let negMotiveE ← withLocalDecl `l BinderInfo.default (mkConst ``Literal) fun lE =>
      mkLambdaFVars #[lE] (mkApp (mkConst ``Not) (mkApp2 (mkConst ``litSatI) IE lE))
    let htE ← mkAppOptM ``List.forall_mem_nil #[some (mkConst ``Literal), some negMotiveE]
    let falseE := mkAppN (mkConst ``upRefutes_sound) #[IE, FE, targetE, hF, htE, hrup]
    m2.assign falseE
  replaceMainGoal []

/-- `nlsat_refute s` — prove `∀ ρ, (∀ C ∈ Cs, clauseHolds ρ atoms C) →
False` from the `s.refutation` snapshot `s` (the F3 DAG walk). -/
elab "nlsat_refute " s:term : tactic => unsafe (do
  let snapTyE ← Term.elabType (← `(SnapshotTy))
  let sE ← Term.elabTerm s (some snapTyE)
  walkRefutation (← getMainGoal) sE)

end Walk
end LeanNonlinearArith.Nlsat
