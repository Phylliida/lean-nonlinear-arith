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
index (G1/G2 + R-b) and the pre-mangle chain-split loop (R-e). -/
inductive FactKind where
  | eqZero (q : MPoly)   -- the fact is `evalP ρ q = 0`
  | neZero (q : MPoly)   -- the fact is `evalP ρ q ≠ 0`
  | eqProdZero (fs : List (MPoly × Bool))
    -- the fact is `((fs.map Prod.fst).map (evalP ρ)).prod = 0` (R-b)
  | negChain (fs : List (MPoly × Bool))
    -- the fact is `negChain ρ fs (¬ sign)` (R-a/R-e): split PRE-mangle
    -- so branch-local zero-product closes see evalP-form facts
  | rootPair (y : Var) (i : Nat) (p : MPoly)
    -- G4 root-atom branch: the fact is `RootAtom.Holds ρ ⟨k, y, i, p⟩`
    -- (the pair `i ≤ rootCount ∧ rootCmp`) — the definite-disc close
    -- (`rootDefiniteClose`) consumes it
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
- `lt`/`gt` negative: the flat `negChain` expansion
  (`negHolds_chain_*`, review 10) — `f₁ = 0 ∨ (… ∨ ¬ sign)` — split by
  the pre-mangle chain loop (R-e, review 12). -/
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
        -- R-b: the `List.prod`-of-evals form is defeq-clean (no
        -- `MPoly.mul`), so this fact DOES enter the zero-product index
        return [(hProd, .eqProdZero fs)]
      else
        let hAll ← mkAppM ``holds_multi_eq_ne #[ρ, fsE, h_i]
        let mappedE := toExpr (fs.map Prod.fst)
        fs.mapM fun (f, _) => do
          let memPrf ← mkDecideProof (← mkAppM ``Membership.mem #[mappedE, toExpr f])
          let hf ← mkAppM' hAll #[toExpr f, memPrf]
          pure (hf, .neZero f)
    | .lt | .gt =>
      if !l.neg then
        -- R-a FULL (review 10): the flat negChain expansion
        -- `f₁ = 0 ∨ (… ∨ ¬ sign)` — split PRE-mangle by the chain
        -- loop (R-e, review 12)
        let lem := match k with
          | .lt => ``negHolds_chain_lt
          | _ => ``negHolds_chain_gt
        let hChain ← mkAppM lem #[ρ, fsE, h_i]
        return [(hChain, .negChain fs)]
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
  | .root ⟨_, y, i, p⟩ =>
    -- G4 root atoms (z3's `mk_root_atom` always arrives negated). The
    -- pair fact (count bound + rootCmp) is the extraction; the
    -- definite-disc close consumes it. Positive-polarity root literals
    -- (`¬atom` failing) stay skipped — sound.
    if !l.neg then return []
    let aE := mkApp IE (toExpr l.bvar)
    let nn ← mkAppOptM ``Classical.not_not #[some aE]
    let hH ← mkAppM ``Iff.mp #[nn, h_i]
    return [(hH, .rootPair y i p)]

/-- The diseq fact for factor `f`, converting from a sign-flipped
fact on `-f` if needed (`evalP_neg` + `neg_ne_zero`; `MPoly.neg`
kernel-reduces so the conversion is defeq-clean). -/
def diseqFactFor (ρ : Expr) (f : MPoly) (fv : FVarId) (flipped : Bool) :
    MetaM Expr := do
  if !flipped then return mkFVar fv
  let fE ← mkAppM ``Check.evalP #[ρ, toExpr f]
  let heq ← mkAppM ``Check.evalP_neg #[ρ, toExpr f]
  let zeroR ← mkAppOptM ``OfNat.ofNat
    #[some (mkConst ``Real), some (toExpr 0), none]
  let neLam ← withLocalDecl `x BinderInfo.default (mkConst ``Real)
    fun xE => do mkLambdaFVars #[xE] (← mkAppM ``Ne #[xE, zeroR])
  let congr ← mkAppM ``congrArg #[neLam, heq]
  let hneg ← mkAppM ``Eq.mp #[congr, mkFVar fv]
  mkAppM ``Iff.mp #[(← mkAppOptM ``neg_ne_zero
    #[some (mkConst ``Real), none, some fE]), hneg]

/-- `∀ f ∈ qs.map Prod.fst, evalP ρ f ≠ 0` from per-factor proofs, via
the `List.forall_mem_cons` fold (binder order `{α} {p} {a} {l}` —
probed 2026-08-09). `qs`/`proofs` must be the same length. -/
partial def forallMemNe (ρ : Expr) (qs : List (MPoly × Bool))
    (proofs : List Expr) : MetaM Expr := do
  let mpolyTy := mkConst ``MPoly   -- the abbrev; defeq to its expansion
  let motiveE ← withLocalDecl `f BinderInfo.default mpolyTy fun fE => do
    let zeroR ← mkAppOptM ``OfNat.ofNat
      #[some (mkConst ``Real), some (toExpr 0), none]
    mkLambdaFVars #[fE] (← mkAppM ``Ne #[(← mkAppM ``Check.evalP #[ρ, fE]), zeroR])
  match qs, proofs with
  | [], [] =>
    mkAppOptM ``List.forall_mem_nil #[some mpolyTy, some motiveE]
  | (f, _) :: rest, pf :: restPf => do
    let restE ← forallMemNe ρ rest restPf
    let mappedTailE := toExpr (rest.map Prod.fst)
    let iffE ← mkAppOptM ``List.forall_mem_cons
      #[some mpolyTy, some motiveE, some (toExpr f), some mappedTailE]
    let andE ← mkAppM ``And.intro #[pf, restE]
    mkAppM ``Iff.mpr #[iffE, andE]
  | _, _ => throwError "forallMemNe: length mismatch"

/-! ## Concrete-coefficient extraction (G4, kernel-checked)

`MPoly.add` is well-founded-compiled, so `coeffsOf` on a concrete
polynomial does NOT reduce under kernel whnf/rfl/decide (probed).
The proof-producing reducer below walks `coeffsOf.go` node-by-node,
using the single-step bridges in `Check/Semantics.lean`
(`MPoly.add_cons_cons_*`, `coeffsOf_go_cons`), with the structural
side equalities (`Monomial.degreeIn`/`erase`, `List.set`/`getElem!`,
Int `beq` chains) discharged by `rfl`-level defeq or `mkDecideProof`
— all kernel-reducible (probed). Every produced term is kernel-
checked; the native values it threads are suggestions only.

The close of the definite-disc family: a `RootAtom.Holds` pair fact
(`i ≤ rootCount ∧ rootCmp`) plus `rootCount = 0` (deg-1/2 with a
decide-grade constant discriminant/coefficient situation) contradicts
the atom's `i ≥ 1` directly. -/

/-- Prove an `Eq` proposition by `rfl`-level defeq (subgoal + assign). -/
def proveByRefl (lhs rhs : Expr) : MetaM Expr := do
  let ty ← mkAppM ``Eq #[lhs, rhs]
  let v ← mkFreshExprMVar ty
  v.mvarId!.refl
  instantiateMVars v

/-- cons-prepend congruence: `h : xs = ys` to `Eq (t :: xs) (t :: ys)`. -/
def consCong (tE : Expr) (h : Expr) : MetaM Expr := do
  let elemTy ← inferType tE
  let xTy := mkApp (mkConst ``List [levelZero]) elemTy
  -- List.cons {α} a as: α (implicit) applied positionally first
  let consAt := mkApp (mkConst ``List.cons [levelZero]) elemTy
  let lam := .lam `x xTy (mkApp2 consAt tE (.bvar 0)) .default
  mkAppM ``congrArg #[lam, h]

/-- The `(base)[k]!` access form (`GetElem?.getElem!` — the elaboration
of the lemmas' own `(coeffsOf p y)[k]!` spelling; probed `pp.all`). -/
def mkIdxGet (base : Expr) (k : Nat) : MetaM Expr :=
  mkAppM ``GetElem?.getElem! #[base, toExpr k]

/-- Proof-producing reduction of `MPoly.add` on concrete polys:
returns `(r, proof of MPoly.add p q = r)`. -/
unsafe def reduceAdd (p q : MPoly) : MetaM (MPoly × Expr) := do
  let pE := toExpr p; let qE := toExpr q
  match p, q with
  | [], q' =>
    return (q', ← mkAppM ``Check.MPoly.add_nil_l #[qE])
  | p', [] =>
    let hne ← mkDecideProof (← mkAppM ``Ne #[pE, toExpr ([] : MPoly)])
    return (p', ← mkAppM ``Check.MPoly.add_nil_r #[pE, hne])
  | (a, m) :: p', (b, n) :: q' =>
    let mE := toExpr m; let nE := toExpr n
    let cmpE ← mkAppM ``Monomial.cmp #[mE, nE]
    match Monomial.cmp m n with
    | .gt =>
      let hcmp ← mkDecideProof (← mkAppM ``Eq #[cmpE, mkConst ``Ordering.gt])
      let hstep ← mkAppM ``Check.MPoly.add_cons_cons_gt #[hcmp]
      let (r', prfR') ← reduceAdd p' ((b, n) :: q')
      let prfCong ← consCong (toExpr (a, m)) prfR'
      return ((a, m) :: r', ← mkAppM ``Eq.trans #[hstep, prfCong])
    | .lt =>
      let hcmp ← mkDecideProof (← mkAppM ``Eq #[cmpE, mkConst ``Ordering.lt])
      let hstep ← mkAppM ``Check.MPoly.add_cons_cons_lt #[hcmp]
      let (r', prfR') ← reduceAdd ((a, m) :: p') q'
      let prfCong ← consCong (toExpr (b, n)) prfR'
      return ((b, n) :: r', ← mkAppM ``Eq.trans #[hstep, prfCong])
    | .eq =>
      let sumE ← mkAppM ``HAdd.hAdd #[toExpr a, toExpr b]
      let beqE ← mkAppM ``BEq.beq #[sumE, toExpr (0 : Int)]
      if a + b == 0 then
        let hz ← mkDecideProof (← mkAppM ``Eq #[beqE, mkConst ``true])
        let hstep ← mkAppM ``Check.MPoly.add_cons_cons_eq_zero
          #[← mkDecideProof (← mkAppM ``Eq #[cmpE, mkConst ``Ordering.eq]), hz]
        let (r', prfR') ← reduceAdd p' q'
        return (r', ← mkAppM ``Eq.trans #[hstep, prfR'])
      else
        let hz ← mkDecideProof (← mkAppM ``Eq #[beqE, mkConst ``false])
        let hstep ← mkAppM ``Check.MPoly.add_cons_cons_eq_ne
          #[← mkDecideProof (← mkAppM ``Eq #[cmpE, mkConst ``Ordering.eq]), hz]
        let (r', prfR') ← reduceAdd p' q'
        let prfCong ← consCong (toExpr ((a + b), m)) prfR'
        return (((a + b), m) :: r', ← mkAppM ``Eq.trans #[hstep, prfCong])

/-- The go-walk: `acc : coeffsOf p y = coeffsOf.go y init ts`. Returns the
final coefficient list and a proof of `coeffsOf p y = <it>`. -/
unsafe def reduceGo (y : Var) (init : List MPoly) (ts : MPoly)
    (acc : Expr) : MetaM (List MPoly × Expr) := do
  let initE := toExpr init; let yE := toExpr y
  match ts with
  | [] =>
    let hEnd ← mkAppM ``Check.coeffsOf.go.eq_1 #[yE, initE]
    return (init, ← mkAppM ``Eq.trans #[acc, hEnd])
  | (a, m) :: ts' =>
    let d := m.degreeIn y
    let v := init[d]!
    let e := m.erase y
    let (w, prfW) ← reduceAdd v [(a, e)]
    let init' := init.set d w
    let init'E := toExpr init'
    let mE := toExpr m
    let hd ← mkDecideProof
      (← mkAppM ``Eq #[← mkAppM ``Monomial.degreeIn #[mE, yE], toExpr d])
    let hv ← proveByRefl (← mkIdxGet initE d) (toExpr v)
    let hset ← proveByRefl
      (← mkAppM ``List.set #[initE, toExpr d, toExpr w]) init'E
    let hstep ← mkAppM ``Check.coeffsOf_go_cons
      #[yE, initE, toExpr a, mE, toExpr ts', toExpr d, toExpr v, toExpr w,
        init'E, hd, hv, prfW, hset]
    let acc' ← mkAppM ``Eq.trans #[acc, hstep]
    reduceGo y init' ts' acc'

/-- Proof-producing coefficient extraction for a concrete polynomial:
returns `(cs, proof of coeffsOf p y = cs)`. -/
unsafe def coeffsOfValue (y : Var) (p : MPoly) : MetaM (List MPoly × Expr) := do
  let pE := toExpr p; let yE := toExpr y
  let d0 := p.degreeIn y
  let init0 : List MPoly := List.replicate (d0 + 1) []
  -- first link: coeffsOf p y = go y (replicate (d0+1) []) p
  let head ← mkAppM ``Check.coeffsOf.eq_def #[pE, yE]
  -- the replicate redex equals the concrete init0 (whnf-structural)
  let repRedex ← mkAppM ``List.replicate
    #[← mkAppM ``HAdd.hAdd #[← mkAppM ``MPoly.degreeIn #[pE, yE],
        toExpr (1 : Nat)], toExpr ([] : MPoly)]
  let hRep ← proveByRefl repRedex (toExpr init0)
  -- lift via congrArg (λ z => go y z p)
  let listMpolyTy := mkApp (mkConst ``List [levelZero]) (mkConst ``MPoly)
  let lam ← withLocalDecl `z BinderInfo.default listMpolyTy fun zE => do
    mkLambdaFVars #[zE] (mkApp3 (mkConst ``Check.coeffsOf.go) yE zE pE)
  let lift ← mkAppM ``congrArg #[lam, hRep]
  let acc0 ← mkAppM ``Eq.trans #[head, lift]
  reduceGo y init0 p acc0

/-- An ℝ-literal zero (the tryZeroProduct spelling). -/
def mkRealZero : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat
    #[some (mkConst ``Real), some (toExpr 0), none]

/-- The discriminant comparison `(a₁)² − 4·(a₂)·(a₃) < 0` from
accessor-building callbacks (uniform spelling across the bridge's
forms). -/
def mkDiscComp (ρ : Expr) (accs : Nat → MetaM Expr) : MetaM Expr := do
  let ev : Nat → MetaM Expr := fun k => do mkAppM ``Check.evalP #[ρ, ← accs k]
  let b ← ev 1; let a ← ev 2; let c ← ev 0
  let bsq ← mkAppM ``HPow.hPow #[b, toExpr (2 : Nat)]
  let fourR ← mkAppOptM ``OfNat.ofNat
    #[some (mkConst ``Real), some (toExpr 4), none]
  let fourA ← mkAppM ``HMul.hMul #[fourR, a]
  let fourAC ← mkAppM ``HMul.hMul #[fourA, c]
  let disc ← mkAppM ``HSub.hSub #[bsq, fourAC]
  let zero ← mkRealZero
  mkAppM ``LT.lt #[disc, zero]

/-- The coefficient-equality `evalP ρ (acc) = 0` from an accessor. -/
def mkCoefZeroComp (ρ : Expr) (acc : MetaM Expr) : MetaM Expr := do
  let ev ← mkAppM ``Check.evalP #[ρ, ← acc]
  let zero ← mkRealZero
  mkAppM ``Eq #[ev, zero]

/-- Close a `< 0` / `= 0` numeric-comparison subgoal whose polys are
concrete: mangle evalP + norm_num. Sandbox-managed by the caller. -/
def closeNumericSubgoal (m : MVarId) : TacticM Unit := do
  let saved ← getGoals
  setGoals [m]
  try
    evalTactic (← `(tactic| simp only [evalP, evalM, evalP_add,
      evalP_mul, evalP_neg, evalP_smulTerm, evalP_ofInt, evalP_ofVar,
      Int.cast_one, Int.cast_ofNat, one_mul, mul_one, add_zero,
      zero_add]))
    evalTactic (← `(tactic| norm_num))
  catch e =>
    setGoals saved
    throw e
  setGoals saved

/-- G4 definite-disc close: for a root-atom pair fact with constant
coefficient data proving no roots exist, close `False` directly.
Returns `true` iff `mvar` was assigned. Lanes: deg-2 const disc < 0;
deg-2 A=B=0; deg-1 A=0. -/
unsafe def rootDefiniteClose (mvar : MVarId) (ρ : Expr)
    (roots : Array (Var × Nat × MPoly × FVarId)) : TacticM Bool := do
  for (y, i, p, hfv) in roots do
    if i == 0 then continue
    let deg := p.degreeIn y
    unless deg == 1 || deg == 2 do continue
    let closed ← mvar.withContext do
      try
        let pE := toExpr p; let yE := toExpr y
        let hdeg ← mkDecideProof
          (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr deg])
        let (cs, hcsPrf) ← coeffsOfValue y p
        let csE := toExpr cs
        -- Two-hop cast for lemma-spelled numeric facts: `congrArg` links
        -- `(coeffsOf p y)` to the concrete `cs` inside the comparison;
        -- an rfl-defeq hop then replaces its `[k]!` accesses with the
        -- concrete coefficients (structural getD computation —
        -- `([1,2,3])[1]! = 2 := rfl` probes green).
        let zTy := mkApp (mkConst ``List [levelZero]) (mkConst ``MPoly)
        let numFact (mkBody : (Nat → MetaM Expr) → MetaM Expr)
            (accsValue : Nat → MetaM Expr) : TacticM Expr := do
          let lam ← withLocalDecl `z BinderInfo.default zTy fun zE => do
            mkLambdaFVars #[zE] (← mkBody (fun k => mkIdxGet zE k))
          let congr ← mkAppM ``congrArg #[lam, hcsPrf]
          let idxForm ← mkBody (fun k => mkIdxGet csE k)
          let valTy ← mkBody accsValue
          let bridge ← proveByRefl idxForm valTy
          let m ← mkFreshExprMVar valTy
          m.mvarId!.withContext do closeNumericSubgoal m.mvarId!
          unless (← m.mvarId!.isAssigned) do
            throwError "rootDefiniteClose: numeric subgoal not closed"
          let hVal ← instantiateMVars m
          let composited ←
            try mkAppM ``Eq.trans #[congr, bridge]
            catch e => throwError "trans: {e.toMessageData}"
          try mkAppM ``Eq.mpr #[composited, hVal]
          catch e => throwError "mpr: {e.toMessageData}"
        let hcount ←
          if deg == 2 && cs.length == 3 then do
            match cs[0]!.asConst?, cs[1]!.asConst?, cs[2]!.asConst? with
            | some C, some B, some A =>
              if B * B - 4 * A * C < 0 then do
                let hdisc ← numFact (fun accs => mkDiscComp ρ accs)
                  (fun k => pure (toExpr (cs[k]!)))
                pure (some (← mkAppM ``Check.rootCount_zero_of_neg_disc
                  #[ρ, yE, pE, hdeg, hdisc]))
              else if A == 0 && B == 0 then do
                let hA ← numFact (fun accs => mkCoefZeroComp ρ (accs 2))
                  (fun _ => pure (toExpr (cs[2]!)))
                let hB ← numFact (fun accs => mkCoefZeroComp ρ (accs 1))
                  (fun _ => pure (toExpr (cs[1]!)))
                pure (some (← mkAppM ``Check.rootCount_zero_of_deg2_lc_zero
                  #[ρ, yE, pE, hdeg, hA, hB]))
              else pure none
            | _, _, _ => pure none
          else if deg == 1 && cs.length == 2 then do
            match cs[1]!.asConst? with
            | some 0 => do
              let hA ← numFact (fun accs => mkCoefZeroComp ρ (accs 1))
                (fun _ => pure (toExpr (cs[1]!)))
              pure (some (← mkAppM ``Check.rootCount_zero_of_deg1_lc_zero
                #[ρ, yE, pE, hdeg, hA]))
            | _ => pure none
          else pure none
        match hcount with
        | none => pure false
        | some hcount =>
          let hHold := mkFVar hfv
          let hle ← mkAppM ``And.left #[hHold]
          let hlof ← mkAppM ``Nat.le_of_eq #[hcount]
          let hp ← mkAppM ``Nat.le_trans #[hle, hlof]
          let hz ← mkAppM ``Nat.eq_zero_of_le_zero #[hp]
          let hne ← mkDecideProof (← mkAppM ``Ne #[toExpr i, toExpr (0 : Nat)])
          let falsePrf ← mkAppOptM ``absurd
            #[none, some (mkConst ``False), hz, hne]
          mvar.assign falsePrf
          let gs ← getGoals
          setGoals (← gs.filterM fun g' => return !(← g'.isAssigned))
          pure true
      catch _ => pure false
    if closed then return true
  return false


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
          oddProd, List.map_cons, List.map_nil, List.prod_cons,
          List.prod_nil, Prod.fst,
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
        let base ← diseqFactFor ρ f fv flipped
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
assigned. The R-b branch handles multi-eq-POSITIVE facts (the
`List.prod`-of-evals form): every factor matched (up to negation) by a
diseq fact ⟹ `List.prod_ne_zero` contradicts the product-vanishing
fact — no factorization needed (the factors are given). -/
unsafe def zeroProductClose (g : MVarId) (ρ : Expr)
    (eqFacts diseqFacts : Array (MPoly × FVarId))
    (prodEqFacts : Array (List (MPoly × Bool) × FVarId)) : TacticM Bool := do
  -- R-b branch: multi-eq-positive facts
  for (fs, h0fv) in prodEqFacts do
    let mut matched : Array (MPoly × FVarId × Bool) := #[]
    let mut ok := true
    for (f, _) in fs do
      match diseqFacts.find? (fun (q, _) => q == f || q == MPoly.neg f) with
      | some (q, fv) => matched := matched.push (f, fv, !(q == f))
      | none => ok := false; break
    if !ok || matched.isEmpty then continue
    let closed ← g.withContext do
      try
        let parts ← matched.toList.mapM fun (f, fv, fl) => diseqFactFor ρ f fv fl
        let hAll ← forallMemNe ρ fs parts
        let hne ← mkAppM ``listEvalProd_ne_zero #[ρ, toExpr fs, hAll]
        let falsePrf ← mkAppOptM ``absurd
          #[none, some (mkConst ``False), mkFVar h0fv, hne]
        g.assign falsePrf
        let gs ← getGoals
        setGoals (← gs.filterM fun g' => return !(← g'.isAssigned))
        return true
      catch _ => return false
    if closed then return true
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
  -- discharge — (poly, h_f fvar) per eq-atom literal. R-b adds the
  -- multi-eq-positive index; R-a collects skipped literals with their
  -- h_i fvars for the conditional sign-collapse pass.
  let mut eqFacts : Array (MPoly × FVarId) := #[]
  let mut diseqFacts : Array (MPoly × FVarId) := #[]
  let mut prodEqFacts : Array (List (MPoly × Bool) × FVarId) := #[]
  let mut chainFacts : Array (FVarId × List (MPoly × Bool)) := #[]
  let mut rootFacts : Array (Var × Nat × MPoly × FVarId) := #[]
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
          | [] => pure (mvar1, true, ((#[], #[], #[], #[], #[]) :
              Array (MPoly × FVarId) × Array (MPoly × FVarId) ×
              Array (List (MPoly × Bool) × FVarId) ×
              Array (FVarId × List (MPoly × Bool)) ×
              Array (Var × Nat × MPoly × FVarId)))
          | facts =>
            let mut mv := mvar1
            let mut eqs : Array (MPoly × FVarId) := #[]
            let mut neqs : Array (MPoly × FVarId) := #[]
            let mut prods : Array (List (MPoly × Bool) × FVarId) := #[]
            let mut chs : Array (FVarId × List (MPoly × Bool)) := #[]
            let mut roots : Array (Var × Nat × MPoly × FVarId) := #[]
            for (fact, kind) in facts do
              let (hfv, mv') ← mv.note `h_f fact none
              mv := mv'
              match kind with
              | .eqZero q => eqs := eqs.push (q, hfv)
              | .neZero q => neqs := neqs.push (q, hfv)
              | .eqProdZero fs => prods := prods.push (fs, hfv)
              | .negChain fs => chs := chs.push (hfv, fs)
              | .rootPair y i p => roots := roots.push (y, i, p, hfv)
              | .other => pure ()
            pure (mv, false, (eqs, neqs, prods, chs, roots))
      | _ =>
        throwError "nlsat_arith_valid: literal {repr l} is undecodable in the atom table"
    mvar := mvar'
    if wasSkipped then skipped := skipped.push l
    match atomsV[l.bvar]? with
    | some (some a) => vars := vars ++ atomVars a
    | _ => pure ()
    eqFacts := eqFacts ++ factInfo.1
    diseqFacts := diseqFacts ++ factInfo.2.1
    prodEqFacts := prodEqFacts ++ factInfo.2.2.1
    chainFacts := chainFacts ++ factInfo.2.2.2.1
    rootFacts := rootFacts ++ factInfo.2.2.2.2
  -- sq_nonneg hints per occurring variable (nlinarith's nonlinear leaf)
  for v in vars.eraseDup do
    mvar ← mvar.withContext do
      let sqn ← mkAppM ``sq_nonneg #[mkApp ρ (toExpr v)]
      let (_, mvar') ← mvar.note `h_sq sqn none
      pure mvar'
  -- G1 zero-product close (review 7, F-v) + R-b multi-eq-positive
  -- branch (review 9): before the simp/ring_nf mangling, while the
  -- h_f facts are still `evalP` comparisons. Shape-gated; no-op on
  -- lt/gt-only cores. (Whole-clause fast path; the R-e chain loop
  -- below re-runs it per branch with the split-produced eq facts.)
  if ← zeroProductClose mvar ρ eqFacts diseqFacts prodEqFacts then
    return
  -- G4 root-atom definite-disc close (census slice): shape-gated;
  -- no-op unless the clause carries a negated root-atom literal whose
  -- constant-coefficient situation kills every root.
  if ← rootDefiniteClose mvar ρ rootFacts then
    return
  -- Unfold evalP/evalM on the concrete polys, then normalize: the
  -- simp-unfold leaves `ρ x ^ 1` powers and `↑(-1)` Int-cast numerals
  -- whose spelling is not linarith-normal (design review 5, F-ii(a)).
  let mangle : TacticM Unit := do
    evalTactic (← `(tactic|
      simp only [evalP, evalM, evalP_add, evalP_mul, evalP_neg, evalP_sub,
        evalP_smulTerm, evalP_ofInt, evalP_ofVar, oddProd, List.map_cons,
        List.map_nil, List.prod_cons, List.prod_nil, Prod.fst, negChain,
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
  -- One not-yet-split Or fact (R-a full, review 10): the `negChain`
  -- expansions of negative multi-factor sign literals. Splitting any
  -- Or hypothesis is sound when proving `False`; the only Or hyps in
  -- this pipeline are the negChain facts (the trichotomy Ors are
  -- consumed immediately on creation).
  let findOr (g : MVarId) (done : Array FVarId) :
      TacticM (Option FVarId) := g.withContext do
    for d in (← getLCtx) do
      if !done.contains d.fvarId then
        let ty ← instantiateMVars d.type
        if ty.isAppOf ``Or then return some d.fvarId
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
      match ← findOr g done with
      | some d =>
        let gs ← g.cases d
        let [c1, c2] := gs.toList.map (·.mvarId) |
          throwError "nlsat_arith_valid: unexpected Or case count"
        closeWithSplits c1 fuel (done.push d)
        closeWithSplits c2 fuel (done.push d)
      | none =>
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
  -- Split fuel sized by the clause (review 11 — no arbitrary bound):
  -- each literal contributes at most `factors + 1` Or-splits (its
  -- negChain depth) and at most one trichotomy split per extracted
  -- diseq fact (bounded by the same count), so 2·(factors+1) per
  -- literal + margin covers every split the loop can make.
  let fuel := CV.foldl (fun acc l =>
    match atomsV[l.bvar]? with
    | some (some (.ineq a)) => acc + 2 * (a.factors.length + 1)
    | _ => acc + 2) 0 + 4
  -- R-e (review 12): split the negChain facts PRE-mangle, one factor
  -- at a time, so each branch keeps evalP-form facts and the
  -- zero-product close can run per branch with the split-produced eq
  -- fact added to the index. Terminal branches: per-branch
  -- zero-product close, then mangle + glue (+ splits) as before.
  -- (`g.cases` whnf's the `negChain` def to the nested Or.)
  let rec chainLoop (g : MVarId) (chs : List (FVarId × List (MPoly × Bool)))
      (eqF : Array (MPoly × FVarId)) : TacticM Unit := do
    setGoals [g]
    match chs with
    | [] =>
      if ← zeroProductClose g ρ eqF diseqFacts prodEqFacts then return
      setGoals [g]
      mangle
      -- NB: the mangle ASSIGNS `g` — the post-mangle goal is a new mvar
      closeWithSplits (← getMainGoal) fuel #[]
    | (_, []) :: rest => chainLoop g rest eqF
    | (fv, f :: frest) :: rest =>
      let gs ← g.cases fv
      let [c1, c2] := gs.toList |
        throwError "nlsat_arith_valid: unexpected negChain case count"
      let fieldFv (c : CasesSubgoal) : TacticM FVarId :=
        match c.fields[0]? with
        | some e =>
          if e.isFVar then pure e.fvarId!
          else throwError "nlsat_arith_valid: negChain field is not an fvar"
        | none => throwError "nlsat_arith_valid: negChain split has no fields"
      let leftFv ← fieldFv c1
      -- left branch: `evalP ρ f.1 = 0` — a new eq fact for the index
      chainLoop c1.mvarId rest (eqF.push (f.1, leftFv))
      -- right branch: `negChain ρ frest tail` — keep splitting
      if frest.isEmpty then
        chainLoop c2.mvarId rest eqF
      else
        let rightFv ← fieldFv c2
        chainLoop c2.mvarId ((rightFv, frest) :: rest) eqF
  if chainFacts.isEmpty then
    setGoals [mvar]
    mangle
    -- NB: the mangle ASSIGNS `mvar` — the post-mangle goal is a new mvar
    closeWithSplits (← getMainGoal) fuel #[]
  else
    chainLoop mvar chainFacts.toList eqFacts

/-- `nlsat_arith_valid` — prove `clauseSatI (interp ρ atoms) C` for a
concrete atom table and clause (the F2 per-arith-marker obligation). -/
elab "nlsat_arith_valid" : tactic => unsafe (do
  proveClauseSat (← getMainGoal))

end Refute
end LeanNonlinearArith.Nlsat
