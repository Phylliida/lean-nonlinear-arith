import Mathlib
import LeanNonlinearArith.Nlsat.Assemble
import LeanNonlinearArith.Nlsat.Coverage

/-!
# nla-19a Slice F2 — the per-bundle arith-lemma elaborator (`Refute`)

The elaborator that discharges, per `.arith core proj` resolution
marker, the validity of the arith lemma:

    clauseSatI (interp ρ atoms) (arithClause core proj)

**Trust shape (R-viii, design review 4):** everything in this file is
UNTRUSTED meta code — it produces proof terms that the kernel checks
against the trusted layer (`Assemble` decode, `Coverage` discharges,
`Check` semantics). Any failure — undecodable literal, unhandled atom
shape, glue failure — is a tactic failure = sound rejection, never an
unsound acceptance.

**Method (per the F2-groundwork analysis):** assume every literal of
the arith clause fails (`hnot : ∀ l ∈ C, ¬ litSatI I l`), extract
ℝ-level facts per literal via the `holds_single_*` collapses
(negated-atom polarity via `Classical.not_not`), unfold `evalP`/`evalM`
on the concrete polys to arithmetic over `ρ`, and close `False` with
`linarith` (workhorse, R-i) / `nlinarith` (backup, with `sq_nonneg`
hints per occurring variable). Step-derived facts (Coverage theorems)
are collected in a later slice — the x0²+x1²<0 refutation's arith
lemmas are all trivially valid and need none.

The elaborator decodes against a NATIVE copy of the atom table
(unsafe-evaluated from the goal — untrusted); proof-term construction
matches by defeq, which the kernel re-verifies.
-/

namespace LeanNonlinearArith.Nlsat

open Check
open Lean Meta Elab Tactic

namespace Refute

/-- Quote a solver literal to its `Expr` (structure-ctor application;
defeq to any elaboration spelling). -/
def litToExpr (l : Literal) : Expr :=
  mkApp2 (mkConst ``Literal.mk) (toExpr l.bvar) (toExpr l.neg)

/-- All variables occurring in a polynomial's monomials. -/
def mpolyVars (p : MPoly) : List Var :=
  p.flatMap fun (_, m) => m.map Prod.fst

/-- All variables occurring anywhere in an atom. -/
def atomVars : Atom → List Var
  | .ineq a => a.factors.flatMap fun (p, _) => mpolyVars p
  | .root a => a.x :: mpolyVars a.p

/-- The fact-extraction result for one literal: the proof term of an
ℝ-level fact, or `none` if the shape is not (yet) handled — skipped
literals weaken the glue but never soundness; the caller reports them
on glue failure. -/
def extractFact (ρ IE : Expr) (h_i : Expr) (l : Literal) (a : Atom) :
    MetaM (Option Expr) := do
  match a with
  | .ineq ⟨k, [(q, false)]⟩ =>
    let qE := toExpr q
    let lem ← match k with
      | .lt => mkAppM ``holds_single_lt #[ρ, qE]
      | .gt => mkAppM ``holds_single_gt #[ρ, qE]
      | .eq => mkAppM ``holds_single_eq #[ρ, qE]
    if l.neg then
      -- h_i : ¬ ¬ H  ⇒  H  ⇒  the ℝ fact
      let aE := mkApp IE (toExpr l.bvar)
      let nn ← mkAppOptM ``Classical.not_not #[some aE]
      let hH ← mkAppM ``Iff.mp #[nn, h_i]
      return some (← mkAppM ``Iff.mp #[lem, hH])
    else
      -- h_i : ¬ H  ⇒  ¬ (the ℝ fact)
      return some (← mkAppM ``mt #[(← mkAppM ``Iff.mpr #[lem]), h_i])
  | _ => return none

/-- Core worker: prove `clauseSatI (interp ρ atoms) C` for concrete
`atoms`, `C`. `hName` seeds the extracted-fact names. Failure (any
undecodable literal, skipped shape, or glue failure) propagates as a
tactic error — the sound direction. `unsafe` for the native decode
(`Meta.evalExpr`) — untrusted meta, the produced terms are
kernel-checked. -/
unsafe def proveClauseSat (mvar : MVarId) : TacticM Unit := do
  let goalType ← mvar.getType
  -- Match `clauseSatI (interp ρ atoms) C` syntactically (no unfolding).
  let (fn, args) := goalType.getAppFnArgs
  unless fn == ``clauseSatI && args.size == 2 do
    throwError "nlsat_arith_valid: goal is not `clauseSatI (interp ρ atoms) C`"
  let IE := args[0]!
  let CE := args[1]!
  let (fnI, argsI) := IE.getAppFnArgs
  unless fnI == ``interp && argsI.size == 2 do
    throwError "nlsat_arith_valid: interpretation is not `interp ρ atoms`"
  let ρ := argsI[0]!
  let atomsE := argsI[1]!
  -- Native copies for decoding (unsafe eval; untrusted).
  let atomsV ← Meta.evalExpr (Array (Option Atom))
    (← Term.elabType (← `(Array (Option Atom)))) atomsE
  let CV ← Meta.evalExpr (List Literal)
    (← Term.elabType (← `(List Literal))) CE
  -- h : ¬ clauseSatI I C
  let [m1] ← mvar.apply (mkConst ``Classical.byContradiction)
    | throwError "nlsat_arith_valid: byContradiction failed"
  let (hFvar, mvar2) ← m1.intro `h
  let mut mvar := mvar2
  let mut skipped : Array Literal := #[]
  let mut vars : List Var := []
  for l in CV do
    -- everything that typechecks terms mentioning context fvars must
    -- run in the CURRENT mvar's local context (hFvar, noted facts)
    let (mvar', wasSkipped) ← mvar.withContext do
      let lE := litToExpr l
      -- h_i : ¬ litSatI I l  :=  fun hlit => h ⟨l, by decide, hlit⟩
      let litSatTy ← mkAppM ``litSatI #[IE, lE]
      let h_i ← withLocalDecl `hl BinderInfo.default litSatTy fun hlit => do
        let memPrf ← mkDecideProof (← mkAppM ``Membership.mem #[CE, lE])
        let andPrf ← mkAppM ``And.intro #[memPrf, hlit]
        -- the ∃ motive is HOU-uninferable; supply it explicitly
        let p ← withLocalDecl `l' BinderInfo.default (mkConst ``Literal) fun lv => do
          let mem ← mkAppM ``Membership.mem #[CE, lv]
          let ls ← mkAppM ``litSatI #[IE, lv]
          mkLambdaFVars #[lv] (← mkAppM ``And #[mem, ls])
        let wit := mkAppN (mkConst ``Exists.intro [levelOne]) #[mkConst ``Literal, p, lE, andPrf]
        mkLambdaFVars #[hlit] (mkApp (mkFVar hFvar) wit)
      let (h_iFvar, mvar1) ← mvar.note `h_i h_i none
      match atomsV[l.bvar]? with
      | some (some a) =>
        mvar1.withContext do
          match (← extractFact ρ IE (mkFVar h_iFvar) l a) with
          | some fact =>
            let (_, mvar2') ← mvar1.note `h_f fact none
            pure (mvar2', false)
          | none => pure (mvar1, true)
      | _ =>
        throwError "nlsat_arith_valid: literal {repr l} is undecodable in the atom table"
    mvar := mvar'
    if wasSkipped then skipped := skipped.push l
    match atomsV[l.bvar]? with
    | some (some a) => vars := vars ++ atomVars a
    | _ => pure ()
  -- sq_nonneg hints per occurring variable (nlinarith's nonlinear leaf)
  for v in vars.eraseDup do
    mvar ← mvar.withContext do
      let sqn ← mkAppM ``sq_nonneg #[mkApp ρ (toExpr v)]
      let (_, mvar') ← mvar.note `h_sq sqn none
      pure mvar'
  replaceMainGoal [mvar]
  -- Unfold evalP/evalM on the concrete polys to arithmetic over ρ,
  -- then the glue: linarith first (R-i), nlinarith as backup.
  evalTactic (← `(tactic|
    simp only [evalP, evalM, evalP_add, evalP_mul, evalP_neg, evalP_sub,
      evalP_smulTerm, evalP_ofInt, evalP_ofVar,
      Int.cast_one, Int.cast_ofNat, one_mul, mul_one, add_zero, zero_add] at *))
  try
    evalTactic (← `(tactic| linarith))
  catch _eLin =>
    try
      evalTactic (← `(tactic| nlinarith []))
    catch _ =>
      let skipMsg := if skipped.isEmpty then "none" else
        (skipped.toList.map (toString ∘ repr)).toString
      throwError "nlsat_arith_valid: glue failed (skipped literals: {skipMsg})"

/-- `nlsat_arith_valid` — prove `clauseSatI (interp ρ atoms) C` for a
concrete atom table and clause (the F2 per-arith-marker obligation). -/
elab "nlsat_arith_valid" : tactic => unsafe (do
  proveClauseSat (← getMainGoal))

end Refute
end LeanNonlinearArith.Nlsat
