import Mathlib
import LeanNonlinearArith.Nlsat.Assemble
import LeanNonlinearArith.Nlsat.Coverage
import LeanNonlinearArith.Nlsat.MPolyFactor

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

**Method (per the F2-groundwork analysis + design review 5):** assume
every literal of the arith clause fails (`hnot : ∀ l ∈ C, ¬ litSatI I l`),
extract ℝ-level facts per literal via the `holds_single_*` collapses
(negated-atom polarity via `Classical.not_not`), unfold `evalP`/`evalM`
on the concrete polys, normalize with `ring_nf` (the simp-unfold leaves
`ρ x ^ 1`/`↑(-1)` spellings that are not linarith-normal — review 5,
F-ii), and close `False` with `linarith` (workhorse, R-i) / `nlinarith`
(backup, with `sq_nonneg` hints per occurring variable). Facts of shape
`¬(t = 0)` are invisible to both (linarith cannot split disequalities),
so on glue failure each is trichotomy-split (`lt_or_gt_of_ne`), lazily,
one at a time, retrying the glue per branch (review 5, F-ii(b); the
acceptance driver's final core 2 needs exactly one split). Step-derived
facts (Coverage theorems) are NOT collected at this layer: review 5's
probe (F-i) showed the acceptance driver's arith lemmas close from
literal-failure facts alone; step-fact collection is re-sequenced to a
later slice driven by a grammar-coverage census.

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

/-- Classification of an extracted ℝ-level fact, for the zero-product
index (G1/G2). -/
inductive FactKind where
  | eqZero (q : MPoly)   -- the fact is `evalP ρ q = 0`
  | neZero (q : MPoly)   -- the fact is `evalP ρ q ≠ 0`
  | other

/-- The fact-extraction for one literal: ℝ-level fact proof terms with
their classifications, or `[]` if the shape is not (yet) handled —
skipped literals weaken the glue but never soundness; the caller
reports them on glue failure. Single-factor all-odd atoms take the
pinned `holds_single_*` path; multi-factor / even-parity atoms
(G2/G3, design review 7) take the `holds_multi_*` path:
- `eq` positive (l.neg): the product vanishes (`holds_multi_eq_prod`);
- `eq` negative: every factor is nonzero (`holds_multi_eq_ne`) — z3's
  `add_zero_assumption` composite `∏ pᵢ ≠ 0` shape;
- `lt`/`gt` positive: the odd-product sign + every factor nonzero;
- `lt`/`gt` negative is disjunctive (some factor vanishes OR the sign
  flips) — skipped (sound; weakens the glue only). -/
def extractFacts (ρ IE : Expr) (h_i : Expr) (l : Literal) (a : Atom) :
    MetaM (List (Expr × FactKind)) := do
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
      let fact ← mkAppM ``Iff.mp #[lem, hH]
      return [(fact, match k with | .eq => .eqZero q | _ => .other)]
    else
      -- h_i : ¬ H  ⇒  ¬ (the ℝ fact)
      let fact ← mkAppM ``mt #[(← mkAppM ``Iff.mpr #[lem]), h_i]
      return [(fact, match k with | .eq => .neZero q | _ => .other)]
  | .ineq ⟨k, fs⟩ =>
    let fsE := toExpr fs
    match k with
    | .eq =>
      if l.neg then
        let aE := mkApp IE (toExpr l.bvar)
        let nn ← mkAppOptM ``Classical.not_not #[some aE]
        let hH ← mkAppM ``Iff.mp #[nn, h_i]
        let hProd ← mkAppM ``holds_multi_eq_prod #[ρ, fsE, hH]
        -- glue-only: the fact's type mentions `factorProd fs`, and
        -- `MPoly.mul` does NOT reduce under kernel whnf (the
        -- kernel-reduction trap), so the zero-product index can't
        -- defeq-match a natively-folded product against it. The mangle
        -- simp set (factorProd + evalP_mul) handles it for the glue.
        return [(hProd, .other)]
      else
        let hAll ← mkAppM ``holds_multi_eq_ne #[ρ, fsE, h_i]
        let mappedE := toExpr (fs.map Prod.fst)
        fs.mapM fun (f, _) => do
          let memPrf ← mkDecideProof (← mkAppM ``Membership.mem #[mappedE, toExpr f])
          let hf ← mkAppM' hAll #[toExpr f, memPrf]
          pure (hf, .neZero f)
    | .lt | .gt =>
      if !l.neg then return []
      let aE := mkApp IE (toExpr l.bvar)
      let nn ← mkAppOptM ``Classical.not_not #[some aE]
      let hH ← mkAppM ``Iff.mp #[nn, h_i]
      let signLem := match k with
        | .lt => ``holds_multi_sign_lt
        | _ => ``holds_multi_sign_gt
      let neLem := match k with
        | .lt => ``holds_multi_allNe_lt
        | _ => ``holds_multi_allNe_gt
      let hSign ← mkAppM signLem #[ρ, fsE, hH]
      let hAll ← mkAppM neLem #[ρ, fsE, hH]
      let mappedE := toExpr (fs.map Prod.fst)
      let perFactor ← fs.mapM fun (f, _) => do
        let memPrf ← mkDecideProof (← mkAppM ``Membership.mem #[mappedE, toExpr f])
        let hf ← mkAppM' hAll #[toExpr f, memPrf]
        pure (hf, .neZero f)
      return (hSign, .other) :: perFactor
  | _ => return []

/-- G1 (design review 7, F-v): the zero-product discharge. If an eq
fact `evalP ρ p = 0` has `p` factorizing natively into factors each
matched (exact poly equality) by a diseq fact `evalP ρ fᵢ ≠ 0`, close
`False` directly: the product identity

    evalP ρ p = ↑c * (evalP ρ f₁)^k₁ * … * (evalP ρ fₘ)^kₘ

is kernel-verified by the evalP simp set + `ring` (the native
factorization is untrusted — a wrong factorization fails loudly here),
and the `mul_ne_zero`/`pow_ne_zero` chain contradicts `p = 0`. This
closes the degree ≥ 3 cases beyond nlinarith's one-round pairwise
products (fs3: three distinct factors; fs4: multiplicity 3).
`unsafe` for consistency with the caller (no native eval here, but the
FVarId-carrying index comes from one). Returns `false` on any
mismatch — the caller falls through to the normal pipeline. -/
unsafe def tryZeroProduct (g : MVarId) (ρ : Expr) (p : MPoly) (h0fv : FVarId)
    (constant : Int) (chain : Array (MPoly × Nat × FVarId × Bool)) : TacticM Bool := do
  g.withContext do
    try
      let ρp ← mkAppM ``Check.evalP #[ρ, toExpr p]
      -- pin R := ℝ explicitly: `Int.cast`'s ring argument is implicit
      -- and the hz subgoal must be ℝ-typed for `ring`
      let mut rhs ← mkAppOptM ``Int.cast
        #[some (mkConst ``Real), none, some (toExpr constant)]
      for (f, k, _, _) in chain do
        let fE ← mkAppM ``Check.evalP #[ρ, toExpr f]
        let fkE ← mkAppM ``HPow.hPow #[fE, toExpr k]
        rhs ← mkAppM ``HMul.hMul #[rhs, fkE]
      let hzTy ← mkAppM ``Eq #[ρp, rhs]
      let hzM ← mkFreshExprMVar hzTy
      let saved ← getGoals
      setGoals [hzM.mvarId!]
      try
        evalTactic (← `(tactic| simp only [evalP, evalM, evalP_add, evalP_mul,
          evalP_neg, evalP_sub, evalP_smulTerm, evalP_ofInt, evalP_ofVar,
          oddProd, factorProd,
          Int.cast_one, Int.cast_ofNat, one_mul, mul_one, add_zero, zero_add]))
        evalTactic (← `(tactic| ring))
      catch e =>
        setGoals saved
        throw e
      setGoals saved
      unless (← hzM.mvarId!.isAssigned) do
        throwError "zero-product identity subgoal not closed"
      let hzE ← instantiateMVars hzM
      -- the ≠ 0 chain, left-nested to match rhs's shape
      let cneInt ← mkDecideProof (← mkAppM ``Ne #[toExpr constant, toExpr (0 : Int)])
      -- `Int.cast_ne_zero`'s binders are all implicit/instance:
      -- {α} [AddGroupWithOne] [CharZero] {n} — pin α := ℝ and n
      let cneIff ← mkAppOptM ``Int.cast_ne_zero
        #[some (mkConst ``Real), none, none, some (toExpr constant)]
      let cne ← mkAppM ``Iff.mpr #[cneIff, cneInt]
      let mut ne := cne
      for (f, k, fv, flipped) in chain do
        -- the diseq fact may be on `-f` (sign-flipped composite factor);
        -- convert via `evalP_neg` + `neg_ne_zero`
        let base ←
          if !flipped then pure (mkFVar fv)
          else do
            let fE ← mkAppM ``Check.evalP #[ρ, toExpr f]
            let heq ← mkAppM ``Check.evalP_neg #[ρ, toExpr f]
            let zeroR ← mkAppOptM ``OfNat.ofNat
              #[some (mkConst ``Real), some (toExpr 0), none]
            let neLam ← withLocalDecl `x BinderInfo.default (mkConst ``Real)
              fun xE => do
                mkLambdaFVars #[xE] (← mkAppM ``Ne #[xE, zeroR])
            let congr ← mkAppM ``congrArg #[neLam, heq]
            let hneg ← mkAppM ``Eq.mp #[congr, mkFVar fv]
            mkAppM ``Iff.mp #[(← mkAppOptM ``neg_ne_zero
              #[some (mkConst ``Real), none, some fE]), hneg]
        let pf ← mkAppM ``pow_ne_zero #[toExpr k, base]
        ne ← mkAppM ``mul_ne_zero #[ne, pf]
      let xeq0 ← mkAppM ``Eq.trans #[(← mkAppM ``Eq.symm #[hzE]), mkFVar h0fv]
      let falsePrf ← mkAppOptM ``absurd #[none, some (mkConst ``False), xeq0, ne]
      g.assign falsePrf
      let gs ← getGoals
      setGoals (← gs.filterM fun g' => return !(← g'.isAssigned))
      return true
    catch _ => return false

/-- Try the zero-product close for each eq fact; `true` if `g` was
assigned. -/
unsafe def zeroProductClose (g : MVarId) (ρ : Expr)
    (eqFacts diseqFacts : Array (MPoly × FVarId)) : TacticM Bool := do
  for (p, h0fv) in eqFacts do
    let fm := MPoly.factorM p
    if fm.constant == 0 || fm.factors.isEmpty then continue
    let mut chain : Array (MPoly × Nat × FVarId × Bool) := #[]
    let mut ok := true
    for (f, k) in fm.factors do
      if k == 0 then continue
      -- exact match OR sign-flipped (z3's factor() normalization aligns
      -- in practice, but a composite atom may carry `-fᵢ`; `MPoly.neg`
      -- kernel-reduces so the conversion is defeq-clean)
      match diseqFacts.find? (fun (q, _) => q == f || q == MPoly.neg f) with
      | some (q, fv) => chain := chain.push (f, k, fv, !(q == f))
      | none => ok := false; break
    if !ok || chain.isEmpty then continue
    if ← tryZeroProduct g ρ p h0fv fm.constant chain then return true
  return false

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
  -- G1 (design review 7): eq/diseq fact index for the zero-product
  -- discharge — (poly, h_f fvar) per eq-atom literal.
  let mut eqFacts : Array (MPoly × FVarId) := #[]
  let mut diseqFacts : Array (MPoly × FVarId) := #[]
  for l in CV do
    -- everything that typechecks terms mentioning context fvars must
    -- run in the CURRENT mvar's local context (hFvar, noted facts)
    let (mvar', wasSkipped, factInfo) ← mvar.withContext do
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
          match (← extractFacts ρ IE (mkFVar h_iFvar) l a) with
          | [] => pure (mvar1, true, (#[] : Array (MPoly × FVarId)), #[])
          | facts =>
            let mut mv := mvar1
            let mut eqs : Array (MPoly × FVarId) := #[]
            let mut neqs : Array (MPoly × FVarId) := #[]
            for (fact, kind) in facts do
              let (hfv, mv') ← mv.note `h_f fact none
              mv := mv'
              match kind with
              | .eqZero q => eqs := eqs.push (q, hfv)
              | .neZero q => neqs := neqs.push (q, hfv)
              | .other => pure ()
            pure (mv, false, eqs, neqs)
      | _ =>
        throwError "nlsat_arith_valid: literal {repr l} is undecodable in the atom table"
    mvar := mvar'
    if wasSkipped then skipped := skipped.push l
    eqFacts := eqFacts ++ factInfo.1
    diseqFacts := diseqFacts ++ factInfo.2
    match atomsV[l.bvar]? with
    | some (some a) => vars := vars ++ atomVars a
    | _ => pure ()
  -- sq_nonneg hints per occurring variable (nlinarith's nonlinear leaf)
  for v in vars.eraseDup do
    mvar ← mvar.withContext do
      let sqn ← mkAppM ``sq_nonneg #[mkApp ρ (toExpr v)]
      let (_, mvar') ← mvar.note `h_sq sqn none
      pure mvar'
  -- G1 zero-product close (review 7, F-v): before the simp/ring_nf
  -- mangling, while the h_f facts are still `evalP` comparisons.
  -- Shape-gated (needs an eq fact whose factors all have diseq facts);
  -- no-op on lt/gt-only cores.
  if ← zeroProductClose mvar ρ eqFacts diseqFacts then
    return
  replaceMainGoal [mvar]
  -- Unfold evalP/evalM on the concrete polys, then normalize: the
  -- simp-unfold leaves `ρ x ^ 1` powers and `↑(-1)` Int-cast numerals
  -- whose spelling is not linarith-normal (design review 5, F-ii(a)).
  evalTactic (← `(tactic|
    simp only [evalP, evalM, evalP_add, evalP_mul, evalP_neg, evalP_sub,
      evalP_smulTerm, evalP_ofInt, evalP_ofVar, oddProd, factorProd,
      Int.cast_one, Int.cast_ofNat, one_mul, mul_one, add_zero, zero_add] at *))
  evalTactic (← `(tactic| ring_nf at *))
  -- The glue: linarith first (R-i), nlinarith as backup. On failure,
  -- lazily trichotomy-split disequality facts `¬(t = 0)` (invisible to
  -- linarith — review 5, F-ii(b)) one at a time, retrying per branch.
  let glue : TacticM Bool := do
    try evalTactic (← `(tactic| linarith)); return true
    catch _ =>
      try evalTactic (← `(tactic| nlinarith [])); return true
      catch _ => return false
  -- One not-yet-split disequality fact of the goal's noted facts.
  let findDiseq (g : MVarId) (done : Array FVarId) :
      TacticM (Option FVarId) := g.withContext do
    for d in (← getLCtx) do
      if d.userName == `h_f && !done.contains d.fvarId then
        let ty ← instantiateMVars d.type
        if ty.isAppOf ``Not && ty.getAppArgs[0]!.isAppOf ``Eq then
          return some d.fvarId
    return none
  -- NOTE: `setGoals`, not `replaceMainGoal` — a closed branch leaves
  -- the goal list EMPTY, and `replaceMainGoal` throws on an empty list.
  let rec closeWithSplits (g : MVarId) (fuel : Nat) (done : Array FVarId) :
      TacticM Unit := do
    setGoals [g]
    if ← glue then return
    match fuel with
    | 0 => throwError "nlsat_arith_valid: glue failed (diseq-split fuel exhausted)"
    | fuel + 1 =>
      match ← findDiseq g done with
      | none =>
        let skipMsg := if skipped.isEmpty then "none" else
          (skipped.toList.map (toString ∘ repr)).toString
        throwError "nlsat_arith_valid: glue failed (skipped literals: {skipMsg})"
      | some d =>
        g.withContext do
          let tri ← mkAppM ``lt_or_gt_of_ne #[mkFVar d]
          let (triFvar, gOr) ← g.note `h_tri tri none
          let gs ← gOr.cases triFvar
          let [c1, c2] := gs.toList.map (·.mvarId) |
            throwError "nlsat_arith_valid: unexpected trichotomy case count"
          closeWithSplits c1 fuel (done.push d)
          closeWithSplits c2 fuel (done.push d)
  closeWithSplits (← getMainGoal) 8 #[]

/-- `nlsat_arith_valid` — prove `clauseSatI (interp ρ atoms) C` for a
concrete atom table and clause (the F2 per-arith-marker obligation). -/
elab "nlsat_arith_valid" : tactic => unsafe (do
  proveClauseSat (← getMainGoal))

end Refute
end LeanNonlinearArith.Nlsat
