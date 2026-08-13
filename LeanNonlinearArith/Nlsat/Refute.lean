import Mathlib
import LeanNonlinearArith.Nlsat.Assemble
import LeanNonlinearArith.Nlsat.Coverage
import LeanNonlinearArith.Nlsat.MPolyFactor
import LeanNonlinearArith.Nlsat.MPolyOps

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

/-- Quote a `RootKind` (no `ToExpr` instance — ctor applications;
defeq to any elaboration spelling). -/
def rootKindToExpr : RootKind → Expr
  | .eq => mkConst ``RootKind.eq
  | .lt => mkConst ``RootKind.lt
  | .gt => mkConst ``RootKind.gt
  | .le => mkConst ``RootKind.le
  | .ge => mkConst ``RootKind.ge

/-- Quote a thomQuadratic step (the only `TraceStep` shape the meta
layer needs an `Expr` of). -/
def thomStepToExpr (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
    (sq sa spd sp : Int) : Expr :=
  mkAppN (mkConst ``TraceStep.thomQuadratic)
    #[rootKindToExpr k, toExpr y, toExpr i, toExpr p,
      toExpr sq, toExpr sa, toExpr spd, toExpr sp]

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
  | rootPair (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
    -- G4 root-atom branch: the fact is `RootAtom.Holds ρ ⟨k, y, i, p⟩`
    -- (the pair `i ≤ rootCount ∧ rootCmp`) — the definite-disc close
    -- (`rootDefiniteClose`) consumes the count side; step-fact
    -- collection (`collectStepFacts`) consumes the comparison side
  | negRoot (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
    -- G11: positive-polarity root literal in the clause (`¬atom`
    -- failing): the fact is `¬ RootAtom.Holds ρ ⟨k, y, i, p⟩` —
    -- the `negRootDeg1Produce` lane converts it into the
    -- `(A = 0) ∨ ¬rootCmp` disjunction (or the full trichotomy when
    -- the lead's sign isn't a clause fact) for the findOr splitter
  | signPos (k : IneqKind) (q : MPoly)
    -- 19b Slice 2: the fact is the POSITIVE comparison
    -- `evalP ρ q < 0` (k = lt) / `0 < evalP ρ q` (k = gt) — the
    -- pseudoDivision lane's A4 lc-sign evidence (`add_lc_ineq`,
    -- nlsat_explain.cpp:1181-1184: the sign-pinning assumption enters
    -- the clause as the negated lt/gt atom on the lc, so its failure
    -- yields exactly these)
  | other

/-- Positive-side extraction (19b Slice 2 split): facts from a proof
`hH` of `Atom.Holds ρ a` directly. This is the `l.neg = true` lane of
`extractFacts` (the clause literal is the negated atom; its failure is
the atom holding) AND the pseudoDivision lane's re-extraction entry
for the transported original-atom `Holds`. -/
def extractPosFacts (ρ : Expr) (a : Atom) (hH : Expr) :
    MetaM (List (Expr × FactKind)) := do
  match a with
  | .ineq ⟨k, [(q, false)]⟩ =>
    let qE := toExpr q
    let lem ← match k with
      | .lt => mkAppM ``holds_single_lt #[ρ, qE]
      | .gt => mkAppM ``holds_single_gt #[ρ, qE]
      | .eq => mkAppM ``holds_single_eq #[ρ, qE]
    let fact ← mkAppM ``Iff.mp #[lem, hH]
    return [(fact, match k with
      | .eq => .eqZero q | .lt => .signPos .lt q | .gt => .signPos .gt q)]
  | .ineq ⟨k, fs⟩ =>
    let fsE := toExpr fs
    match k with
    | .eq =>
      let hProd ← mkAppM ``holds_multi_eq_prod #[ρ, fsE, hH]
      -- R-b: the `List.prod`-of-evals form is defeq-clean (no
      -- `MPoly.mul`), so this fact DOES enter the zero-product index
      return [(hProd, .eqProdZero fs)]
    | .lt | .gt =>
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
  | .root ⟨k, y, i, p⟩ =>
    -- G4 root atoms (z3's `mk_root_atom` always arrives negated). The
    -- pair fact (count bound + rootCmp) is the extraction; the
    -- definite-disc close consumes it.
    return [(hH, .rootPair k y i p)]

/-- Negative-side extraction: facts from a proof `hNH` of
`¬ Atom.Holds ρ a` (the `l.neg = false` lane of `extractFacts`, and
the pseudoDivision lane's transported `¬Holds`). -/
def extractNegFacts (ρ : Expr) (a : Atom) (hNH : Expr) :
    MetaM (List (Expr × FactKind)) := do
  match a with
  | .ineq ⟨k, [(q, false)]⟩ =>
    let qE := toExpr q
    let lem ← match k with
      | .lt => mkAppM ``holds_single_lt #[ρ, qE]
      | .gt => mkAppM ``holds_single_gt #[ρ, qE]
      | .eq => mkAppM ``holds_single_eq #[ρ, qE]
    let fact ← mkAppM ``mt #[(← mkAppM ``Iff.mpr #[lem]), hNH]
    return [(fact, match k with | .eq => .neZero q | _ => .other)]
  | .ineq ⟨k, fs⟩ =>
    let fsE := toExpr fs
    match k with
    | .eq =>
      let hAll ← mkAppM ``holds_multi_eq_ne #[ρ, fsE, hNH]
      let mappedE := toExpr (fs.map Prod.fst)
      fs.mapM fun (f, _) => do
        let memPrf ← mkDecideProof (← mkAppM ``Membership.mem #[mappedE, toExpr f])
        let hf ← mkAppM' hAll #[toExpr f, memPrf]
        pure (hf, .neZero f)
    | .lt | .gt =>
      -- R-a FULL (review 10): the flat negChain expansion
      -- `f₁ = 0 ∨ (… ∨ ¬ sign)` — split PRE-mangle by the chain
      -- loop (R-e, review 12)
      let lem := match k with
        | .lt => ``negHolds_chain_lt
        | _ => ``negHolds_chain_gt
      let hChain ← mkAppM lem #[ρ, fsE, hNH]
      return [(hChain, .negChain fs)]
  | .root ⟨k, y, i, p⟩ =>
    -- G11: positive-polarity root literal in the clause (`¬atom`
    -- failing): the `¬ Holds` fact.
    return [(hNH, .negRoot k y i p)]

/-- The fact-extraction for one literal: ℝ-level fact proof terms with
their classifications, or `[]` if the shape is not (yet) handled —
skipped literals weaken the glue but never soundness; the caller
reports them on glue failure. Dispatches on the literal polarity to
the positive/negative extractions (the `not_not`/`mt` dance at the
`litSatI` seam lives here only). -/
def extractFacts (ρ IE : Expr) (h_i : Expr) (l : Literal) (a : Atom) :
    MetaM (List (Expr × FactKind)) := do
  if l.neg then
    let aE := mkApp IE (toExpr l.bvar)
    let nn ← mkAppOptM ``Classical.not_not #[some aE]
    let hH ← mkAppM ``Iff.mp #[nn, h_i]
    extractPosFacts ρ a hH
  else
    extractNegFacts ρ a h_i

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
      signMatches,
      Int.cast_one, Int.cast_ofNat, one_mul, mul_one, add_zero,
      zero_add]))
    evalTactic (← `(tactic| norm_num))
  catch e =>
    setGoals saved
    throw e
  setGoals saved

/-- The two-hop value-fact bridge (G4 census): a proposition over the
coefficient accessors `(coeffsOf p y)[k]!`, transported from its VALUE
form over the reducer's concrete `cs` list. `mkBody` builds the
proposition from arbitrary accessors (uniform spelling across the
lemma-spelled and `[k]!`-redex forms); `accsValue` builds it from the
concrete value accessors. The value-side subgoal is discharged by
`closeNumericSubgoal` — the natively suggested values are suggestions
only; every link is kernel-checked. -/
def mkValueFact (hcsPrf : Expr) (cs : List MPoly)
    (mkBody : (Nat → MetaM Expr) → MetaM Expr)
    (accsValue : Nat → MetaM Expr) : TacticM Expr := do
  let zTy := mkApp (mkConst ``List [levelZero]) (mkConst ``MPoly)
  let csE := toExpr cs
  let lam ← withLocalDecl `z BinderInfo.default zTy fun zE => do
    mkLambdaFVars #[zE] (← mkBody (fun k => mkIdxGet zE k))
  let congr ← mkAppM ``congrArg #[lam, hcsPrf]
  let idxForm ← mkBody (fun k => mkIdxGet csE k)
  let valTy ← mkBody accsValue
  let bridge ← proveByRefl idxForm valTy
  let m ← mkFreshExprMVar valTy
  m.mvarId!.withContext do closeNumericSubgoal m.mvarId!
  let hVal ← instantiateMVars m
  -- hasMVar, not just isAssigned: a failing norm_num can leave the
  -- mvar assigned to a term with a hole (see closeAlgRefl's docstring)
  if hVal.hasMVar then
    throwError "mkValueFact: numeric subgoal not closed"
  let composited ←
    try mkAppM ``Eq.trans #[congr, bridge]
    catch e => throwError "trans: {e.toMessageData}"
  try mkAppM ``Eq.mpr #[composited, hVal]
  catch e => throwError "mpr: {e.toMessageData}"

/-- G4 definite-disc close: for a root-atom pair fact with constant
coefficient data proving no roots exist, close `False` directly.
Returns `true` iff `mvar` was assigned. Lanes: deg-2 const disc < 0;
deg-2 A=B=0; deg-1 A=0. -/
unsafe def rootDefiniteClose (mvar : MVarId) (ρ : Expr)
    (roots : Array (RootKind × Var × Nat × MPoly × FVarId)) : TacticM Bool := do
  for (_k, y, i, p, hfv) in roots do
    if i == 0 then continue
    let deg := p.degreeIn y
    unless deg == 1 || deg == 2 do continue
    let closed ← mvar.withContext do
      try
        let pE := toExpr p; let yE := toExpr y
        let hdeg ← mkDecideProof
          (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr deg])
        let (cs, hcsPrf) ← coeffsOfValue y p
        -- Two-hop cast for lemma-spelled numeric facts: `congrArg` links
        -- `(coeffsOf p y)` to the concrete `cs` inside the comparison;
        -- an rfl-defeq hop then replaces its `[k]!` accesses with the
        -- concrete coefficients (structural getD computation —
        -- `([1,2,3])[1]! = 2 := rfl` probes green).
        let numFact (mkBody : (Nat → MetaM Expr) → MetaM Expr)
            (accsValue : Nat → MetaM Expr) : TacticM Expr := do
          mkValueFact hcsPrf cs mkBody accsValue
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

/-! ## G4 census slice, item 3 — step-fact collection (the cross-links
member)

The census's design column (BOARD G4): live drivers are all
literal-local, but one member of the emission grammar is NOT — an arith
clause whose contradiction needs `rootVal`-vs-`ρ y` orderings CONNECTED
to ineq-atom signs, where the encoding literal may be absent from the
clause. The root fact extraction (item 2) yields opaque
`rootCmp k (ρ y) (rootVal ρ y i p)` comparisons (`rootVal` carries
`sqrt`): the glue can't consume them. The bundle's encoding steps are
the bridge: each step that encodes a root literal the clause carries
(matched by `(k, y, i, p)`) converts the root comparison into
first-order comparison/s facts:

- **linearRoot**: through `coverage_linearRoot` — the emitted literal's
  failure is exactly the root comparison, so the comparison reversal
  gives a plain `evalP`-level sign fact (the `lin_root_*` family behind
  the discharge).
- **thomQuadratic**: through `coverage_thomQuadratic` — the root
  comparison IS the evaluated Thom region formula; forwarded through
  the iff it becomes an Or/And of comparisons over
  `evalP ρ p` / the `2Ay+B` value data, then lead-resolved (via
  `leadSgn_of_pos`/`leadSgn_of_neg`, from a numeric or clause-literal
  lead sign) and coefficient-reduced (via the reducer's `hcsPrf`
  bridge — the `MPoly.add` kernel-reduction trap again), so the
  mangle's `thomFormula` unfold turns it into glue-ready comparisons.
  The disjunctive cases are consumed by `closeWithSplits`'s existing
  Or-split (`findOr`).

Every produced fact is a kernel-checked term; a step whose evidence is
missing (canonicity unchecked, grammar inconsistency, missing clause
sign literal in the non-const lanes) is SKIPPED — facts are additive,
never subtractive (sound; the walk rejects only if a load-bearing step
was skipped). Payload decision data (`sq`/`sa`/`mkNeg`/`lcFact`) is
consumed only after GRAMMATICAL verification; the grammar prop for
linearRoot can't ride `decide` (`coeffsIn` hits the `MPoly.add`
wf-compilation wall), so it is constructed from the reducer chain +
`coeffsOf_getElem!_eq`.
-/

/-- Find a determining comparison fact `0 < evalP ρ q` (sign 1),
`evalP ρ q < 0` (sign −1), or `evalP ρ q = 0` / `0 = evalP ρ q`
(sign 0) on the target poly `q` among the extracted `h_f` facts of the
current goal's local context. Native poly match against each fact's
evalP argument (defeq-checked); the result carries the fact fvar and
the fact's own value spelling. -/
unsafe def findSignFact (ρ : Expr) (q : MPoly) :
    TacticM (Option (Int × Expr × Expr)) := do
  let vE ← mkAppM ``Check.evalP #[ρ, toExpr q]
  let zR ← mkRealZero
  for d in (← getLCtx) do
    unless d.userName == `h_f do continue
    let ty ← instantiateMVars d.type
    let (fn, args) := ty.getAppFnArgs
    if fn == ``LT.lt && args.size == 4 then
      let a := args[2]!; let b := args[3]!
      let aZero ← isDefEq a zR
      if aZero then
        if ← isDefEq b vE then return some (1, mkFVar d.fvarId, b)
      let bZero ← isDefEq b zR
      if bZero then
        if ← isDefEq a vE then return some (-1, mkFVar d.fvarId, a)
    if fn == ``Eq && args.size == 3 then
      let a := args[1]!; let b := args[2]!
      if ← isDefEq a vE then
        if ← isDefEq b zR then return some (0, mkFVar d.fvarId, a)
      if ← isDefEq a zR then
        if ← isDefEq b vE then return some (0, mkFVar d.fvarId, b)
  return none

/-- Convert a determining comparison proof on `v` into a proof of
`signMatches s v` for the concrete payload sign −1/0/1. The
`signMatches` body is the bare disjunction `A ∨ B ∨ C`; the unused
sides' Props are pinned explicitly (no HOU mvars). -/
def mkSignMatchesOfComp (s : Int) (vE : Expr) (hcomp : Expr) : MetaM Expr := do
  let sE := toExpr s
  let tyOf (t : Int) (cmp : MetaM Expr) : MetaM Expr := do
    let eq ← mkAppM ``Eq #[sE, toExpr t]
    mkAppM ``And #[eq, ← cmp]
  let zR ← mkRealZero
  let ltL ← mkAppM ``LT.lt #[vE, zR]   -- v < 0  (side A / s = −1)
  let eqZ ← mkAppM ``Eq #[vE, zR]     -- v = 0  (side B / s = 0)
  let ltR ← mkAppM ``LT.lt #[zR, vE]   -- 0 < v  (side C / s = 1)
  match s with
  | 1 => do
    let hs ← mkEqRefl (toExpr (1 : Int))
    let hAnd ← mkAppM ``And.intro #[hs, hcomp]
    let aTy ← tyOf (-1) (pure ltL)
    let bTy ← tyOf 0 (pure eqZ)
    let hBC ← mkAppOptM ``Or.inr #[some bTy, none, hAnd]
    mkAppOptM ``Or.inr #[some aTy, none, hBC]
  | -1 => do
    let hs ← mkEqRefl (toExpr (-1 : Int))
    let hAnd ← mkAppM ``And.intro #[hs, hcomp]
    let bTy ← tyOf 0 (pure eqZ)
    let cTy ← tyOf 1 (pure ltR)
    mkAppOptM ``Or.inl #[none, some (← mkAppM ``Or #[bTy, cTy]), hAnd]
  | 0 => do
    let hs ← mkEqRefl (toExpr (0 : Int))
    let hAnd ← mkAppM ``And.intro #[hs, hcomp]
    let aTy ← tyOf (-1) (pure ltL)
    let cTy ← tyOf 1 (pure ltR)
    let hBC ← mkAppOptM ``Or.inl #[none, some cTy, hAnd]
    mkAppOptM ``Or.inr #[some aTy, none, hBC]
  | _ => throwError "mkSignMatchesOfComp: sign {s} out of range"

/-- The congruence-transport helper at the level of the reducer bridge:
given `hcsPrf : coeffsOf p y = cs`, produce
`F((coeffsOf p y)[k]!) = F(cs[k]!)` for any `F` (Prop- or value-valued)
— the two-hop `congrArg` + `rfl`-defeq chain (the kernel-reduction
trap discipline; the native `cs` indexing is suggestion only). -/
def mkCoeFactEq (hcsPrf : Expr) (cs : List MPoly) (k : Nat)
    (F : Expr → MetaM Expr) : MetaM Expr := do
  let zTy := mkApp (mkConst ``List [levelZero]) (mkConst ``MPoly)
  let lam ← withLocalDecl `z BinderInfo.default zTy fun zE => do
    mkLambdaFVars #[zE] (← F (← mkIdxGet zE k))
  let t1 ← mkAppM ``congrArg #[lam, hcsPrf]
  let hget0 ← proveByRefl (← mkIdxGet (toExpr cs) k) (toExpr cs[k]!)
  -- Pin the proof's type to `cs[k]!-listget = cs[k]!-MPoly`: the raw
  -- refl term's INTRINSIC type keeps the list-get redex spelling, and
  -- an `evalP` application of that redex stalls the mangle's
  -- simp-unfold downstream (the equations only fire on cons literals)
  let hget ← mkExpectedTypeHint hget0
    (← mkAppM ``Eq #[← mkIdxGet (toExpr cs) k, toExpr cs[k]!])
  let mpty := mkConst ``MPoly
  let lam2 ← withLocalDecl `x BinderInfo.default mpty fun xE => do
    mkLambdaFVars #[xE] (← F xE)
  let t2 ← mkAppM ``congrArg #[lam2, hget]
  mkAppM ``Eq.trans #[t1, t2]

/-- Identity proof function on a proposition (for `Or.imp`/`And.imp`
components that keep their spelling). -/
def idLam (ty : Expr) : MetaM Expr :=
  withLocalDecl `hz BinderInfo.default ty fun hzE => mkLambdaFVars #[hzE] hzE

/-- The two lead-sign proof transports for the deg-1 lanes:
`((0 < acc) → (0 < conc), (acc < 0) → (conc < 0))`, where `hAE` is the
`mkCoeFactEq` bridge `evalP ρ (coeffsOf p y)[1]! = evalP ρ cs[1]!`.
Needed because the accessor redex stalls the mangle's `evalP`
simp-unfold, leaving an opaque atom where the dead-end split leaf was
supposed to die on the sign conjunct (review F-ii). -/
def mkSignTransports (ρ pE yE : Expr) (hAE : Expr) : MetaM (Expr × Expr) := do
  let accE ← mkIdxGet (← mkAppM ``Check.coeffsOf #[pE, yE]) 1
  let accValE ← mkAppM ``Check.evalP #[ρ, accE]
  let zR ← mkRealZero
  let posLam ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE] (← mkAppM ``LT.lt #[zR, zE])
  let negLam ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE] (← mkAppM ``LT.lt #[zE, zR])
  -- hAE : accessor = concrete; `Eq.mp` transports FORWARD (acc → conc)
  let posTr ← withLocalDecl `hz BinderInfo.default
    (← mkAppM ``LT.lt #[zR, accValE]) fun hzE => do
    mkLambdaFVars #[hzE] (← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[posLam, hAE]), hzE])
  let negTr ← withLocalDecl `hz BinderInfo.default
    (← mkAppM ``LT.lt #[accValE, zR]) fun hzE => do
    mkLambdaFVars #[hzE] (← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[negLam, hAE]), hzE])
  pure (posTr, negTr)

/-- Same two-hop transport as `mkValueFact`, but the value-side proof is
SUPPLIED (the clause-literal lanes — no numeric close needed). -/
def mkValueFactOf (hcsPrf : Expr) (cs : List MPoly)
    (mkBody : (Nat → MetaM Expr) → MetaM Expr)
    (accsValue : Nat → MetaM Expr) (hVal : Expr) : TacticM Expr := do
  let zTy := mkApp (mkConst ``List [levelZero]) (mkConst ``MPoly)
  let csE := toExpr cs
  let lam ← withLocalDecl `z BinderInfo.default zTy fun zE => do
    mkLambdaFVars #[zE] (← mkBody (fun k => mkIdxGet zE k))
  let congr ← mkAppM ``congrArg #[lam, hcsPrf]
  let idxForm ← mkBody (fun k => mkIdxGet csE k)
  let bridge ← proveByRefl idxForm (← mkBody accsValue)
  let composited ← mkAppM ``Eq.trans #[congr, bridge]
  mkAppM ``Eq.mpr #[composited, hVal]

/-- A numerically-closed fact of the given proposition (value-side;
concrete `cs` spellings — the R-i reducer currency). -/
def closeNumerically (tgt : Expr) : TacticM Expr := do
  -- `withoutModifyingState`: a failing `norm_num` leaves the sandbox
  -- mvar assigned to a holed chain (see closeAlgRefl's docstring) —
  -- roll the mvar table back so the dead entry can't corrupt
  -- downstream term production (19b Slice 2).
  withoutModifyingState do
    let m ← mkFreshExprMVar tgt
    m.mvarId!.withContext do closeNumericSubgoal m.mvarId!
    let h ← instantiateMVars m
    -- hasMVar, not just isAssigned (see closeAlgRefl's docstring)
    if h.hasMVar then
      throwError "closeNumerically: numeric subgoal not closed"
    pure h

/-- Close an `Eq` between ℝ value expressions whose polys are concrete
spelling variants of one value (mangle `evalP` + `ring`) — the
disc-expansion transfer lane. Sandbox-managed by the caller.

Trap (19b Slice 1, pd-corruption probe): `ring` assigns the goal with
its normalization chain BEFORE the final close, so a failure can leave
the mvar assigned to a term with a HOLE (an unassigned sub-mvar) while
the elaborator only logs the error — the `isAssigned` check alone then
"accepts" a false equation (kernel would still reject the holed term
downstream, but the clean skip discipline needs the throw HERE). The
`hasMVar` check on the produced term is the robust guard. -/
def closeAlgRefl (tgt : Expr) : TacticM Expr := do
  let saved ← getGoals
  try
    let h ← withoutModifyingState do
      let m ← mkFreshExprMVar tgt
      setGoals [m.mvarId!]
      m.mvarId!.withContext do
        evalTactic (← `(tactic| simp only [evalP, evalM, evalP_add, evalP_mul,
          evalP_neg, evalP_smulTerm, evalP_ofInt, evalP_ofVar, Int.cast_one,
          Int.cast_ofNat, one_mul, mul_one, add_zero, zero_add]))
        evalTactic (← `(tactic| ring))
      let h ← instantiateMVars m
      if h.hasMVar then
        throwError "closeAlgRefl: subgoal not closed"
      pure h
    setGoals saved
    pure h
  catch e =>
    -- restore the goal list on throw (the closeNumericSubgoal
    -- pattern) — else the sandbox mvar leaks into the caller's
    -- tactic state (review finding, 19b Slice 1). The
    -- `withoutModifyingState` additionally rolls back the mvar
    -- assignments: a failing `ring` leaves the sandbox mvar assigned
    -- to a normalization chain with ring-internal `_tmp` fvars, and
    -- the polluted table entry corrupted downstream term production
    -- (19b Slice 2, the corrupt-payload probes).
    setGoals saved
    throw e

/-- 19b Slice 1: the pseudo-division identity for one emitted step,
re-proved per-instance (decision 1 — z3's own mathematical contract
`lc^d · f = Q·eq + r`, polynomial.cpp:5095, never the payload's
say-so). Q is recomputed natively (`pseudoDivisionCore …
quotient=true`, untrusted suggestion — `partial`, native-only by
construction); the payload's OWN `d`/`r` are used: any (d, Q, r)
witness of the identity with lc ≠ 0 yields the same sign conclusions
(the perturbation (d+1, lc·Q, lc·r) scales sign r and flips parity in
cancellation), so matching the recomputation is unnecessary. The
identity is stated at the value level — `(evalP ρ lc)^d · evalP ρ f =
evalP ρ Q · evalP ρ eq + evalP ρ r` with `lc = (eq.coeffsIn x)[k]!`
the CONCRETE leading coefficient (no kernel-pow, no lcPowMul poly —
the literal exponent is ring-native) — and kernel-closed by the
closeAlgRefl/zeroProductClose idiom (evalP simp + `ring`, complete
for these identities). Returns `(lc, identity-proof)`. Throws on
failure (corrupt payload — the caller's catch skips soundly). -/
unsafe def pseudoDivisionIdentity (ρ : Expr) (f eq : MPoly) (x : Var)
    (d : Nat) (r : MPoly) : TacticM (MPoly × Expr) := do
  let k := eq.degreeIn x
  let lc := (eq.coeffsIn x)[k]!
  let (_, q, _) := MPoly.pseudoDivisionCore f eq x false true
  let lcValE ← mkAppM ``Check.evalP #[ρ, toExpr lc]
  let fValE ← mkAppM ``Check.evalP #[ρ, toExpr f]
  let qValE ← mkAppM ``Check.evalP #[ρ, toExpr q]
  let eqValE ← mkAppM ``Check.evalP #[ρ, toExpr eq]
  let rValE ← mkAppM ``Check.evalP #[ρ, toExpr r]
  let powE ← mkAppM ``HPow.hPow #[lcValE, toExpr d]
  let lhs ← mkAppM ``HMul.hMul #[powE, fValE]
  let rhs ← mkAppM ``HAdd.hAdd #[(← mkAppM ``HMul.hMul #[qValE, eqValE]), rValE]
  let hId ← closeAlgRefl (← mkAppM ``Eq #[lhs, rhs])
  pure (lc, hId)

/-- The `Grammar (.linearRoot …)` proof for a concrete linearRoot step.
Kernel `decide` cannot go through `grammarOK`'s `coeffsIn` branch (the
`MPoly.add` wf-compilation wall), so the coefficient evidence chain is
built from the reducer + `coeffsOf_getElem!_eq`. Throws on
payload/grammar inconsistency (sound skip — the caller catches). -/
unsafe def mkLinearRootGrammar (k : RootKind) (y : Var) (p : MPoly) (mkNeg : Bool)
    (lcFact : Option (MPoly × Int)) : TacticM Expr := do
  let pE := toExpr p; let yE := toExpr y
  let hdeg ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr (1 : Nat)])
  let (cs, hcsPrf) ← coeffsOfValue y p
  unless cs.length == 2 do
    throwError "mkLinearRootGrammar: coefficient count {cs.length} ≠ 2"
  let c1 := cs[1]!
  -- the array/list accessor bridge: (p.coeffsIn y)[1]! = c₁
  let hb1 ← mkAppM ``coeffsOf_getElem!_eq #[pE, yE, toExpr (1 : Nat)]
  let hc1 ← mkCoeFactEq hcsPrf cs 1 (fun x => pure x)
  let harr ← mkAppM ``Eq.trans #[(← mkAppM ``Eq.symm #[hb1]), hc1]
  match lcFact with
  | none => do
    let some v := c1.asConst?
      | throwError "mkLinearRootGrammar: none-lcFact but lc is not const"
    let someVE ← mkAppM ``Option.some #[toExpr v]
    let hAs ← proveByRefl (← mkAppM ``MPoly.asConst? #[toExpr c1]) someVE
    let lam ← withLocalDecl `x BinderInfo.default (mkConst ``MPoly) fun xE => do
      mkLambdaFVars #[xE] (← mkAppM ``Eq
        #[(← mkAppM ``MPoly.asConst? #[xE]), someVE])
    -- congrArg on the prop-family: (asConst? lhs = some v) = (asConst? rhs = some v)
    let ha ← mkAppM ``Eq.mpr #[(← mkAppM ``congrArg #[lam, harr]), hAs]
    let hv ← mkDecideProof (← mkAppM ``Ne #[toExpr v, toExpr (0 : Int)])
    let ltE ← mkAppM ``LT.lt #[toExpr v, toExpr (0 : Int)]
    let decideE ← mkAppOptM ``decide #[some ltE, none]
    let hmk ← mkAppM ``Eq.symm
      #[← mkDecideProof (← mkAppM ``Eq #[decideE, toExpr mkNeg])]
    let motiveE ← withLocalDecl `v0 BinderInfo.default (mkConst ``Int) fun v0E => do
      let asC ← mkAppM ``Eq
        #[← mkAppM ``MPoly.asConst?
            #[← mkIdxGet (← mkAppM ``MPoly.coeffsIn #[pE, yE]) 1],
          ← mkAppM ``Option.some #[v0E]]
      let hvNe ← mkAppM ``Ne #[v0E, toExpr (0 : Int)]
      let hlt ← mkAppM ``LT.lt #[v0E, toExpr (0 : Int)]
      let hdec0 ← mkAppOptM ``decide #[some hlt, none]
      let hmkT ← mkAppM ``Eq #[toExpr mkNeg, hdec0]
      mkLambdaFVars #[v0E] (← mkAppM ``And #[asC, ← mkAppM ``And #[hvNe, hmkT]])
    let hAnd ← mkAppM ``And.intro #[ha, ← mkAppM ``And.intro #[hv, hmk]]
    let hcond ← mkAppOptM ``Exists.intro
      #[none, some motiveE, some (toExpr v), some hAnd]
    mkAppOptM ``Grammar.linearRoot
      #[some (rootKindToExpr k), some yE, some pE, some (toExpr mkNeg),
        some (toExpr lcFact), hdeg, hcond]
  | some (c, s) => do
    unless c1 == c do
      throwError "mkLinearRootGrammar: lcFact poly is not the lc"
    let cE := toExpr c; let sE := toExpr s
    let hc ← mkAppM ``Eq.symm #[harr]
    let hsne ← mkDecideProof (← mkAppM ``Ne #[sE, toExpr (0 : Int)])
    let hmk ← mkAppM ``Eq.symm #[← mkDecideProof (← mkAppM ``Eq
      #[(← mkAppOptM ``decide #[some (← mkAppM ``LT.lt #[sE, toExpr (0 : Int)]), none]),
        toExpr mkNeg])]
    -- the const-sign conjunct: ∀ v, c.asConst? = some v → s = Int.sign v
    let hsig ← withLocalDecl `v BinderInfo.default (mkConst ``Int) fun vE0 => do
      let hty ← mkAppM ``Eq
        #[(← mkAppM ``MPoly.asConst? #[cE]), ← mkAppM ``Option.some #[vE0]]
      withLocalDecl `h BinderInfo.default hty fun hE => do
        match c.asConst? with
        | none => do
          -- vacuous: h conflicts with the rfl-known `none`
          let hN ← proveByRefl (← mkAppM ``MPoly.asConst? #[cE])
            (toExpr (none : Option Int))
          let hconf ← mkAppM ``Eq.trans #[(← mkAppM ``Eq.symm #[hN]), hE]
          let tgt ← mkAppM ``Eq #[sE, ← mkAppM ``Int.sign #[vE0]]
          let hne ← mkAppM ``Ne.symm #[← mkAppM ``Option.some_ne_none #[vE0]]
          let body ← mkAppOptM ``absurd
            #[some (← mkAppM ``Eq #[(toExpr (none : Option Int)),
                  (← mkAppM ``Option.some #[vE0])]),
              some tgt, hconf, hne]
          mkLambdaFVars #[vE0, hE] body
        | some v0 => do
          -- c.asConst? = some v0: chain h : some v0 = some vE0
          let hP ← proveByRefl (← mkAppM ``MPoly.asConst? #[cE])
            (← mkAppM ``Option.some #[toExpr v0])
          let hv0v ← mkAppM ``Eq.trans #[(← mkAppM ``Eq.symm #[hP]), hE]
          let hvv ← mkAppM ``Option.some.inj #[hv0v]
          let hs0 ← mkDecideProof
            (← mkAppM ``Eq #[sE, ← mkAppM ``Int.sign #[toExpr v0]])
          let signLam ← withLocalDecl `w BinderInfo.default (mkConst ``Int) fun wE => do
            mkLambdaFVars #[wE] (← mkAppM ``Int.sign #[wE])
          let body ← mkAppM ``Eq.trans #[hs0, ← mkAppM ``congrArg #[signLam, hvv]]
          mkLambdaFVars #[vE0, hE] body
    let hcond ← mkAppM ``And.intro
      #[hc, ← mkAppM ``And.intro #[hsne, ← mkAppM ``And.intro #[hmk, hsig]]]
    mkAppOptM ``Grammar.linearRoot
      #[some (rootKindToExpr k), some yE, some pE, some (toExpr mkNeg),
        some (toExpr lcFact), hdeg, hcond]

/-- The lc-sign evidence lambda for `coverage_linearRoot`:
`∀ c s, lcFact = some (c, s) → c.asConst? = none → signMatches s (evalP
ρ c)`. `lcFact = none`: the arm is dead at the first hypothesis
(`none ≠ some`). Const `c`: the arm is dead at the second (`asConst?`
rfl-evals to `some`). Non-const `c`: the clause sign literal (the z3
`ensure_sign` emission; an extracted `h_f` fact) is converted to
`signMatches` and transported through the some-injection. Throws when
the non-const lane's clause fact is missing or sign-inconsistent (sound
skip — the caller catches). -/
unsafe def mkHlcLambda (ρ : Expr) (lcFact : Option (MPoly × Int)) : TacticM Expr := do
  match lcFact with
  | none => do
    let noneE := toExpr (none : Option (MPoly × Int))
    withLocalDecl `c BinderInfo.default (mkConst ``MPoly) fun cE => do
    withLocalDecl `s BinderInfo.default (mkConst ``Int) fun sE => do
      let prodE ← mkAppM ``Prod.mk #[cE, sE]
      let someE ← mkAppM ``Option.some #[prodE]
      let h1Ty ← mkAppM ``Eq #[noneE, someE]
      withLocalDecl `h1 BinderInfo.default h1Ty fun h1E => do
        let h2Ty ← mkAppM ``Eq
          #[(← mkAppM ``MPoly.asConst? #[cE]), toExpr (none : Option Int)]
        withLocalDecl `h2 BinderInfo.default h2Ty fun h2E => do
          let tgt ← mkAppM ``signMatches #[sE, ← mkAppM ``Check.evalP #[ρ, cE]]
          let hne ← mkAppM ``Ne.symm #[← mkAppM ``Option.some_ne_none #[prodE]]
          let body ← mkAppOptM ``absurd #[some h1Ty, some tgt, h1E, hne]
          mkLambdaFVars #[cE, sE, h1E, h2E] body
  | some (c, s) => do
    let prodTy := mkApp2 (mkConst ``Prod [levelZero, levelZero])
      (mkConst ``MPoly) (mkConst ``Int)
    let compLane? ←
      match c.asConst? with
      | none => do
        -- the clause-literal lane: signMatches at the CONST value `c`
        -- from the extracted `h_f` comparison
        match ← findSignFact ρ c with
        | none => throwError "mkHlcLambda: no clause sign fact for the lc"
        | some (sgn, hcomp, vE) =>
          unless sgn == s do
            throwError "mkHlcLambda: lc sign {sgn} ≠ payload {s}"
          pure (some (← mkSignMatchesOfComp sgn vE hcomp))
      | some _ => pure none
    withLocalDecl `cv BinderInfo.default (mkConst ``MPoly) fun cvE => do
    withLocalDecl `sv BinderInfo.default (mkConst ``Int) fun svE => do
      let prodE ← mkAppM ``Prod.mk #[cvE, svE]
      let someE ← mkAppM ``Option.some #[prodE]
      let h1Ty ← mkAppM ``Eq #[toExpr (some (c, s) : Option (MPoly × Int)), someE]
      withLocalDecl `h1 BinderInfo.default h1Ty fun h1E => do
        let h2Ty ← mkAppM ``Eq
          #[(← mkAppM ``MPoly.asConst? #[cvE]), toExpr (none : Option Int)]
        withLocalDecl `h2 BinderInfo.default h2Ty fun h2E => do
          let tgt ← mkAppM ``signMatches #[svE, ← mkAppM ``Check.evalP #[ρ, cvE]]
          let hEq ← mkAppM ``Option.some.inj #[h1E]
          let body ← match compLane? with
          | some hVal => do
            -- transport `signMatches s (evalP ρ c)` along the injection
            let prodLam ← withLocalDecl `w BinderInfo.default prodTy fun wE => do
              let pe ← mkAppM ``Prod.fst #[wE]
              let se ← mkAppM ``Prod.snd #[wE]
              mkLambdaFVars #[wE]
                (← mkAppM ``signMatches #[se, ← mkAppM ``Check.evalP #[ρ, pe]])
            let htransport ← mkAppM ``congrArg #[prodLam, hEq]
            mkAppM ``Eq.mp #[htransport, hVal]
          | none => do
            -- const lane: the arm is dead on h2 — transport the `none`
            -- contradiction from cvE to c via the fst-projection
            let some v0 := c.asConst? | throwError "mkHlcLambda: lane mismatch"
            let hP ← proveByRefl (← mkAppM ``MPoly.asConst? #[toExpr c])
              (← mkAppM ``Option.some #[toExpr v0])
            let fstLam ← withLocalDecl `z BinderInfo.default prodTy fun zE => do
              mkLambdaFVars #[zE] (← mkAppM ``Prod.fst #[zE])
            let hcv2 ← mkAppM ``Eq.symm #[← mkAppM ``congrArg #[fstLam, hEq]]
            let eqnLam ← withLocalDecl `w BinderInfo.default (mkConst ``MPoly) fun wE => do
              mkLambdaFVars #[wE]
                (← mkAppM ``Eq #[(← mkAppM ``MPoly.asConst? #[wE]),
                  toExpr (none : Option Int)])
            let htyeq ← mkAppM ``congrArg #[eqnLam, hcv2]
            let h2v ← mkAppM ``Eq.mp #[htyeq, h2E]
            let hconf ← mkAppM ``Eq.trans #[(← mkAppM ``Eq.symm #[hP]), h2v]
            let hne ← mkAppM ``Option.some_ne_none #[toExpr v0]
            mkAppOptM ``absurd #[some (← mkAppM ``Eq
                #[(← mkAppM ``Option.some #[toExpr v0]), toExpr (none : Option Int)]),
              some tgt, hconf, hne]
          mkLambdaFVars #[cvE, svE, h1E, h2E] body

/-- Shared tail of the linearRoot productions: given the coverage
iftarget (`hcmp : rootCmp k (ρ y) (rootVal ρ y i p)`) plus the step's
grammar/canonicity/lc evidence, derive and note the emitted-literal
comparison. -/
unsafe def linearProduceTail (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (p : MPoly) (mkNeg : Bool) (hcmp hcov : Expr) : TacticM MVarId := do
  let hSL ← mkAppM ``Iff.mpr #[hcov, hcmp]
  -- collapse `¬ SHolds` to the comparison (emitted atom computed
  -- natively via `linearRootEmitted` = (k.toIneqSign, parity fold))
  let (k', lsign) := k.toIneqSign
  let q := if mkNeg then p.neg else p
  let qE := toExpr q
  let lem ← match k' with
    | IneqKind.lt => mkAppM ``holds_single_lt #[ρ, qE]
    | IneqKind.gt => mkAppM ``holds_single_gt #[ρ, qE]
    | IneqKind.eq => mkAppM ``holds_single_eq #[ρ, qE]
  let hcomp ←
    if !lsign then
      -- polarity `true`: ¬ SHolds ρ a true = ¬ ¬ Holds — forward the
      -- double negation, then the single-factor collapse. The Holds
      -- proposition is rebuilt natively (the em projections would
      -- otherwise have to survive a whnf chain).
      let kE' := match k' with
        | IneqKind.lt => mkConst ``IneqKind.lt
        | IneqKind.gt => mkConst ``IneqKind.gt
        | IneqKind.eq => mkConst ``IneqKind.eq
      let fsE := toExpr [(q, false)]
      let atomE := mkApp2 (mkConst ``IneqAtom.mk) kE' fsE
      let propE ← mkAppM ``IneqAtom.Holds #[ρ, atomE]
      let hH ← mkAppM ``Iff.mp
        #[(← mkAppOptM ``Classical.not_not #[some propE]), hSL]
      mkAppM ``Iff.mp #[lem, hH]
    else do
      -- polarity `false`: ¬ SHolds ρ a false = ¬ Holds — mt of the
      -- single-factor collapse
      mkAppM ``mt #[(← mkAppM ``Iff.mpr #[lem]), hSL]
  let hsN := Name.mkSimple s!"hS{n}"
  let (_, mvar') ← mvar.note hsN hcomp none
  pure mvar'

/-- linearRoot step consumption: for a root fact `⟨k, y, i, p⟩` encoded
by a `linearRoot` step, convert the root comparison into the step's
emitted-literal sign comparison (a plain ℝ fact the glue consumes).
Skips (throws) on any missing evidence — grammar, canonicity, or the
non-const lc lane's clause fact. -/
unsafe def linearStepProduce (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (y : Var) (i : Nat) (p : MPoly) (mkNeg : Bool)
    (lcFact : Option (MPoly × Int)) (hfvR : FVarId) : TacticM MVarId := do
  let pE := toExpr p
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``MPoly.canonOK) pE, mkConst ``true])
  let hcan ← mkAppM ``MPoly.canonOK_sound #[pE, hOK]
  let hgram ← mkLinearRootGrammar k y p mkNeg lcFact
  let hlc ← mkHlcLambda ρ lcFact
  let hcov ← mkAppM ``coverage_linearRoot
    #[ρ, rootKindToExpr k, toExpr y, toExpr i, pE, toExpr mkNeg, toExpr lcFact,
      hgram, hcan, hlc]
  let hcmp ← mkAppM ``And.right #[mkFVar hfvR]
  linearProduceTail mvar ρ n k p mkNeg hcmp hcov

/-- The sa = 0 degenerate reroute (z3 `mk_quadratic_root` :811-812, E1):
the clause's root atom is on the PARENT `p` (deg 2 in `y`), the step is
`linearRoot` on the reduct `q = B·y + C` (`lcFact` = some `(c, s)`).
The vanishing-A evidence comes from the clause's `A = 0` sign literal;
the coefficient links `q`'s two coefficients are the parent's (natively
checked, kernel-chained). -/
unsafe def linearStepProduceDeg (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (y : Var) (i : Nat) (parent q : MPoly) (mkNeg : Bool)
    (lcFact : Option (MPoly × Int)) (hfvR : FVarId) : TacticM MVarId := do
  let pE := toExpr parent; let yE := toExpr y; let iE := toExpr i; let qE := toExpr q
  let (cs, hcsPrf) ← coeffsOfValue y parent
  let (csQ, hcsPrfQ) ← coeffsOfValue y q
  unless cs.length == 3 && csQ.length == 2 && cs[1]! == csQ[1]! && cs[0]! == csQ[0]! do
    throwError "linearStepProduceDeg: q is not the reduct of the parent"
  let A := cs[2]!
  let valAccsP : Nat → MetaM Expr := fun k => pure (toExpr (cs[k]!))
  let zR ← mkRealZero
  -- the vanishing-A fact from the clause's `A = 0` sign literal
  let hcompA ←
    match ← findSignFact ρ A with
    | none => throwError "linearStepProduceDeg: no clause A = 0 fact"
    | some (0, hcomp, _) => pure hcomp
    | some (sgn, _, _) =>
      throwError "linearStepProduceDeg: A fact has sign {sgn} ≠ 0"
  let hA0 ← mkValueFactOf hcsPrf cs (fun accs => do
      mkAppM ``Eq #[← mkAppM ``Check.evalP #[ρ, ← accs 2], zR])
    valAccsP hcompA
  let hdeg2 ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr (2 : Nat)])
  let hdeg1 ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[qE, yE], toExpr (1 : Nat)])
  let hdeg ← mkAppM ``rootVal_eq_degenerate #[ρ, yE, iE, pE, hdeg2, hA0]
  -- coefficient links: evalP of the parent's [j]! = evalP of q's [j]!
  let link (j : Nat) : MetaM Expr := do
    let hP ← mkCoeFactEq hcsPrf cs j (fun v => mkAppM ``Check.evalP #[ρ, v])
    let hQ ← mkCoeFactEq hcsPrfQ csQ j (fun v => mkAppM ``Check.evalP #[ρ, v])
    mkAppM ``Eq.trans #[hP, ← mkAppM ``Eq.symm #[hQ]]
  let link0 ← link 0
  let link1 ← link 1
  -- hdiv : -Cp0 / Cp1 = -Cq0 / Cq1 (both divisions over the ACCESSOR
  -- forms, nested two-leg congruence so the middle terms match)
  let negL ← withLocalDecl `x BinderInfo.default (mkConst ``Real) fun xE => do
    mkLambdaFVars #[xE] (← mkAppM ``Neg.neg #[xE])
  let hnegc ← mkAppM ``congrArg #[negL, link0]
  let coeP1E ← mkAppM ``Check.evalP #[ρ, ← mkIdxGet (← mkAppM ``Check.coeffsOf #[pE, yE]) 1]
  let coeQ0E ← mkAppM ``Check.evalP #[ρ, ← mkIdxGet (← mkAppM ``Check.coeffsOf #[qE, yE]) 0]
  let divL1 ← withLocalDecl `x BinderInfo.default (mkConst ``Real) fun xE => do
    mkLambdaFVars #[xE] (← mkAppM ``HDiv.hDiv #[xE, coeP1E])
  let hdiv1 ← mkAppM ``congrArg #[divL1, hnegc]
  let negCoeQ0E ← mkAppM ``Neg.neg #[coeQ0E]
  let divL2 ← withLocalDecl `x BinderInfo.default (mkConst ``Real) fun xE => do
    mkLambdaFVars #[xE] (← mkAppM ``HDiv.hDiv #[negCoeQ0E, xE])
  let hdiv2 ← mkAppM ``congrArg #[divL2, link1]
  let hdiv ← mkAppM ``Eq.trans #[hdiv1, hdiv2]
  let htailQ ← mkAppM ``rootVal_eq_linear #[ρ, yE, iE, qE, hdeg1]
  let hrv ← mkAppM ``Eq.trans
    #[(← mkAppM ``Eq.trans #[hdeg, hdiv]), ← mkAppM ``Eq.symm #[htailQ]]
  -- transport the root comparison across the rootVal equality
  let cmpL ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE]
      (mkAppN (mkConst ``rootCmp) #[rootKindToExpr k, mkApp ρ yE, zE])
  let hcmp' ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[cmpL, hrv]),
    (← mkAppM ``And.right #[mkFVar hfvR])]
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``MPoly.canonOK) qE, mkConst ``true])
  let hcan ← mkAppM ``MPoly.canonOK_sound #[qE, hOK]
  let hgram ← mkLinearRootGrammar k y q mkNeg lcFact
  let hlc ← mkHlcLambda ρ lcFact
  let hcov ← mkAppM ``coverage_linearRoot
    #[ρ, rootKindToExpr k, yE, iE, qE, toExpr mkNeg, toExpr lcFact,
      hgram, hcan, hlc]
  linearProduceTail mvar ρ n k q mkNeg hcmp' hcov

/-- The encoding-free lane (foreign traces, grammar-free): a deg-1 root
fact with a CONSTANT nonzero lead coefficient converts unconditionally
via `rootVal_eq_linear` + `linearRoot_discharge` — no bundle step
needed. (z3's own production routes const-lc deg-1 roots through
`mk_linear_root`, so this region is foreign-trace defense; the
non-const skip is sound.) -/
unsafe def rootGenericLinearProduce (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (y : Var) (i : Nat) (p : MPoly) (hfvR : FVarId) :
    TacticM MVarId := do
  let pE := toExpr p; let yE := toExpr y; let iE := toExpr i
  unless p.degreeIn y == 1 && i == 1 do
    throwError "rootGenericLinearProduce: not a deg-1 root-1 fact"
  let (cs, hcsPrf) ← coeffsOfValue y p
  unless cs.length == 2 do
    throwError "rootGenericLinearProduce: coefficient count {cs.length} ≠ 2"
  let some v := cs[1]!.asConst?
    | throwError "rootGenericLinearProduce: lc is not const"
  unless v != 0 do
    throwError "rootGenericLinearProduce: lc is zero"
  let mkNeg := decide (v < 0)
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``MPoly.canonOK) pE, mkConst ``true])
  let hcan ← mkAppM ``MPoly.canonOK_sound #[pE, hOK]
  let hdeg ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr (1 : Nat)])
  let oneR ← mkAppOptM ``OfNat.ofNat
    #[some (mkConst ``Real), some (toExpr (1 : Nat)), none]
  let negOneR ← mkAppM ``Neg.neg #[oneR]
  let mult := if mkNeg then negOneR else oneR
  let hAq ← mkValueFact hcsPrf cs
    (fun accs => do
      let ev ← mkAppM ``Check.evalP #[ρ, ← accs 1]
      let mulT ← mkAppM ``HMul.hMul #[mult, ev]
      mkAppM ``LT.lt #[(← mkRealZero), mulT])
    (fun k => pure (toExpr (cs[k]!)))
  let hiff ← mkAppM ``linearRoot_discharge
    #[ρ, rootKindToExpr k, yE, pE, toExpr mkNeg, hdeg, hcan, hAq]
  let hrveq ← mkAppM ``rootVal_eq_linear #[ρ, yE, iE, pE, hdeg]
  let cmpL ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE]
      (mkAppN (mkConst ``rootCmp) #[rootKindToExpr k, mkApp ρ yE, zE])
  let hcmp' ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[cmpL, hrveq]),
    (← mkAppM ``And.right #[mkFVar hfvR])]
  linearProduceTail mvar ρ n k p mkNeg hcmp' hiff

/-- The production `rootGeneric` lane (G11): a `rootGeneric` bundle
step on a deg-1 poly, matched to an extracted root fact `(k, y, 1, p)`
— the vanishing-**non-const**-lc production case (o139's cid 7, the
case review 15's production-unreachability argument missed; the
encoding-free lane deliberately skips non-const lcs). Converts the
opaque root comparison through the uniform identity
(`linearNonconst_aux`, sign-matched `S·(A·y + C)` form): with a clause
sign fact for the lead, `linearRootNonconst{Pos,Neg}_discharge` gives
the direct first-order comparison `0 ⋈ evalP ρ p` (z3's own
`mk_linear_root` encoding shape); without one,
`linearRootNonconst_disjunction` gives the two-sign Or the findOr
splitter consumes. Const-lc throws (the encoding-free lane's region —
no duplication). -/
unsafe def rootGenericStepProduce (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (y : Var) (i : Nat) (p : MPoly) (hfvR : FVarId) :
    TacticM MVarId := do
  let pE := toExpr p; let yE := toExpr y; let iE := toExpr i
  unless p.degreeIn y == 1 && i == 1 do
    throwError "rootGenericStepProduce: not a deg-1 root-1 fact"
  let (cs, hcsPrf) ← coeffsOfValue y p
  unless cs.length == 2 do
    throwError "rootGenericStepProduce: coefficient count {cs.length} ≠ 2"
  let aPoly := cs[1]!
  if aPoly.asConst?.isSome then
    throwError "rootGenericStepProduce: const lc is the encoding-free lane's region"
  let hdeg ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr (1 : Nat)])
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``MPoly.canonOK) pE, mkConst ``true])
  let hcan ← mkAppM ``MPoly.canonOK_sound #[pE, hOK]
  let hholds ← mkAppM ``And.left #[mkFVar hfvR]
  -- the comparison, transported through rootVal_eq_linear
  let hrveq ← mkAppM ``rootVal_eq_linear #[ρ, yE, iE, pE, hdeg]
  let cmpL ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE]
      (mkAppN (mkConst ``rootCmp) #[rootKindToExpr k, mkApp ρ yE, zE])
  let hcmp' ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[cmpL, hrveq]),
    (← mkAppM ``And.right #[mkFVar hfvR])]
  -- the lead's sign fact decides the lane (accessor-spelling antecedents
  -- via the two-hop reducer bridge, as in the thom lane)
  let hAE ← mkCoeFactEq hcsPrf cs 1 (fun v => mkAppM ``Check.evalP #[ρ, v])
  let zR ← mkRealZero
  match ← findSignFact ρ aPoly with
  | none =>
    let hdisj ← mkAppM ``linearRootNonconst_disjunction
      #[ρ, rootKindToExpr k, yE, pE, hdeg, hcan, hholds, hcmp']
    -- the sign conjuncts' accessor redex stalls the mangle's evalP
    -- unfold — and the dead-end leaf dies ON the sign conjunct, so
    -- transport both to the concrete spelling (review F-ii)
    let (posTr, negTr) ← mkSignTransports ρ pE yE hAE
    let (_, dArgs) := (← inferType hdisj).getAppFnArgs
    let (_, a0) := dArgs[0]!.getAppFnArgs
    let (_, a1) := dArgs[1]!.getAppFnArgs
    let g2 ← mkAppM ``And.imp #[posTr, ← idLam a0[1]!]
    let g3 ← mkAppM ``And.imp #[negTr, ← idLam a1[1]!]
    let hnew ← mkAppM ``Or.imp #[g2, g3, hdisj]
    let (_, mv) ← mvar.note (Name.mkSimple s!"hS{n}") hnew none
    pure mv
  | some (0, _, _) =>
    -- a clause `A = 0` fact contradicts `ne_of_one_le_rootCount_deg1`
    -- (the Holds pair's count side forces the lead nonzero). Note the
    -- lead's `< 0 ∨ > 0` trichotomy in the concrete spelling: the bare
    -- diseq is invisible to linarith, but the findOr splitter consumes
    -- the Or and each branch dies on the `A = 0` fact. (Review F-i:
    -- the previous "nothing to add — the glue closes via that diseq
    -- clash" comment overclaimed; NOTHING produced the diseq, and
    -- `rootDefiniteClose` only covers the literal-zero lc.)
    let hAne ← mkAppM ``ne_of_one_le_rootCount_deg1 #[ρ, yE, pE, hdeg, hholds]
    let neL ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
      mkLambdaFVars #[zE] (← mkAppM ``Ne #[zE, zR])
    let hAneC ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[neL, hAE]), hAne]
    let htri ← mkAppM ``lt_or_gt_of_ne #[hAneC]
    let (_, mv) ← mvar.note (Name.mkSimple s!"hS{n}") htri none
    pure mv
  | some (sgn, hcomp, _vE) =>
    unless sgn == 1 || sgn == -1 do throwError "rootGenericStepProduce: sign {sgn}"
    -- transport the sign fact from concrete-poly to accessor spelling:
    -- hAE : accessor = concrete and `Eq.mpr` transports BACKWARD
    -- (β → α), taking the concrete-spelled clause fact to the
    -- accessor spelling the discharges want
    let cmpA ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
      if sgn == 1 then
        mkLambdaFVars #[zE] (← mkAppM ``LT.lt #[zR, zE])
      else
        mkLambdaFVars #[zE] (← mkAppM ``LT.lt #[zE, zR])
    let hcmpA ← mkAppM ``Eq.mpr #[(← mkAppM ``congrArg #[cmpA, hAE]), hcomp]
    let hiff ←
      if sgn == 1 then
        mkAppM ``linearRootNonconstPos_discharge
          #[ρ, rootKindToExpr k, yE, pE, hdeg, hcan, hholds, hcmpA]
      else
        mkAppM ``linearRootNonconstNeg_discharge
          #[ρ, rootKindToExpr k, yE, pE, hdeg, hcan, hholds, hcmpA]
    let hnew ← mkAppM ``Iff.mp #[hiff, hcmp']
    let (_, mv) ← mvar.note (Name.mkSimple s!"hS{n}") hnew none
    pure mv

/-- The negative-side lane (G11): a positive-in-clause root literal at
deg 1 (`negRoot` fact, `¬ RootAtom.Holds`) converts into a plain
disjunction — `negHolds_deg1_disjunction` gives `(A = 0) ∨ ¬rootCmp`,
then the two disjuncts are brought into glue form on the spot: the
A-side via the reducer bridge (accessor → concrete coeff poly), the
comparison side via `Iff.not` on the sign-matched
`linearRootNonconst{Pos,Neg}_discharge` when the lead has a clause sign
fact (else the full trichotomy fallback `negHolds_deg1_trichotomy` —
review F-ii; a clause `A = 0` fact makes the literal vacuous and the
lane skips). No deferred discharge at split time: the findOr
splitter's branches get plain first-order facts. Not matched to any
step — the conversion is semantic. -/
unsafe def negRootDeg1Produce (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (y : Var) (i : Nat) (p : MPoly) (hfvN : FVarId) :
    TacticM MVarId := do
  let pE := toExpr p; let yE := toExpr y
  unless p.degreeIn y == 1 && i == 1 do
    throwError "negRootDeg1Produce: not a deg-1 root-1 fact"
  let (cs, hcsPrf) ← coeffsOfValue y p
  unless cs.length == 2 do
    throwError "negRootDeg1Produce: coefficient count {cs.length} ≠ 2"
  let aPoly := cs[1]!
  let hdeg ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr (1 : Nat)])
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``MPoly.canonOK) pE, mkConst ``true])
  let hcan ← mkAppM ``MPoly.canonOK_sound #[pE, hOK]
  let hdisj ← mkAppM ``negHolds_deg1_disjunction
    #[ρ, rootKindToExpr k, yE, pE, hdeg, mkFVar hfvN]
  let zR ← mkRealZero
  -- first disjunct: accessor → concrete coeff poly spelling; take the
  -- accessor spelling from the disjunction's own LHS type (`Or`'s args
  -- are #[A, B]: [0]! = accessor-eq, [1]! = the ¬rootCmp disjunct)
  let hAE ← mkCoeFactEq hcsPrf cs 1 (fun v => mkAppM ``Check.evalP #[ρ, v])
  let eqL ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE] (← mkAppM ``Eq #[zE, zR])
  let (_, disjArgs) := (← inferType hdisj).getAppFnArgs
  let lhsE := disjArgs[0]!
  let f0 ← withLocalDecl `hz BinderInfo.default lhsE fun hzE => do
    -- hAE : accessor = concrete, so `Eq.mp` transports hz (accessor-eq)
    -- to the concrete coeff-poly spelling the glue's sign facts use
    let t ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[eqL, hAE]), hzE]
    mkLambdaFVars #[hzE] t
  -- second disjunct: sign-locked `Iff.not` conversion; the no-sign-fact
  -- case takes the full trichotomy fallback (review F-ii — z3 emits the
  -- deg-1 non-const-lc root atom with NO lc guard, so the sign is not
  -- structurally present in the clause)
  let nrcTy := disjArgs[1]!
  let fallback : TacticM MVarId := do
    let h3 ← mkAppM ``negHolds_deg1_trichotomy
      #[ρ, rootKindToExpr k, yE, pE, hdeg, hcan, mkFVar hfvN]
    -- f0 transports the `A = 0` disjunct; the sign conjuncts of the
    -- two sign disjuncts go through the same bridge (their accessor
    -- redex stalls the mangle — review F-ii)
    let (posTr, negTr) ← mkSignTransports ρ pE yE hAE
    let (_, args3) := (← inferType h3).getAppFnArgs
    let (_, rArgs) := args3[1]!.getAppFnArgs
    let (_, c1) := rArgs[0]!.getAppFnArgs
    let (_, c2) := rArgs[1]!.getAppFnArgs
    let g2 ← mkAppM ``And.imp #[posTr, ← idLam c1[1]!]
    let g3 ← mkAppM ``And.imp #[negTr, ← idLam c2[1]!]
    let hnew ← mkAppM ``Or.imp #[f0, (← mkAppM ``Or.imp #[g2, g3]), h3]
    let (_, mv) ← mvar.note (Name.mkSimple s!"hN{n}") hnew none
    pure mv
  match ← findSignFact ρ aPoly with
  | some (0, _, _) =>
    -- a clause `A = 0` fact makes the literal VACUOUS (`¬ Holds` holds
    -- trivially: the root count is 0) — the other literals carry the
    -- close; noting the disjunction would only buy a wasted split
    pure mvar
  | some (sgn, hcomp, _) =>
    if sgn == 1 || sgn == -1 then do
      -- accessor-form sign evidence (the same reducer bridge as
      -- rootGenericStepProduce), then the sign-matched discharge
      let cmpA ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
        if sgn == 1 then
          mkLambdaFVars #[zE] (← mkAppM ``LT.lt #[zR, zE])
        else
          mkLambdaFVars #[zE] (← mkAppM ``LT.lt #[zE, zR])
      -- hAE : accessor = concrete; `Eq.mpr` transports BACKWARD, so
      -- the concrete-spelled clause sign fact lands in the accessor
      -- spelling the discharges want (same idiom as
      -- rootGenericStepProduce)
      let hcmpA ← mkAppM ``Eq.mpr #[(← mkAppM ``congrArg #[cmpA, hAE]), hcomp]
      -- lc ≠ 0 ⟹ rootCount = 1 (the discharges' `_hholds` argument)
      let hAne ←
        if sgn == 1 then mkAppM ``ne_of_gt #[hcmpA]
        else mkAppM ``ne_of_lt #[hcmpA]
      let hrc ← mkAppM ``rootCount_one_of_deg1_lc_ne #[ρ, yE, pE, hdeg, hAne]
      let hle ← mkAppM ``le_of_eq #[← mkAppM ``Eq.symm #[hrc]]
      let hiff ←
        if sgn == 1 then
          mkAppM ``linearRootNonconstPos_discharge
            #[ρ, rootKindToExpr k, yE, pE, hdeg, hcan, hle, hcmpA]
        else
          mkAppM ``linearRootNonconstNeg_discharge
            #[ρ, rootKindToExpr k, yE, pE, hdeg, hcan, hle, hcmpA]
      let hniff ← mkAppM ``Iff.not #[hiff]
      let f2 ← withLocalDecl `hz BinderInfo.default nrcTy fun hzE => do
        mkLambdaFVars #[hzE] (← mkAppM ``Iff.mp #[hniff, hzE])
      let hnew ← mkAppM ``Or.imp #[f0, f2, hdisj]
      let (_, mv) ← mvar.note (Name.mkSimple s!"hN{n}") hnew none
      pure mv
    else fallback -- dead defense (findSignFact returns 0/±1 only)
  | none => fallback

/-- The grammar prop for a thomQuadratic step: coefficient-free (degree
+ sign ranges only), so the plain `grammarOK` decide ticket works. -/
def mkThomGrammar (k : RootKind) (y : Var) (i : Nat) (p : MPoly)
    (sq sa spd sp : Int) : MetaM Expr := do
  let sE := thomStepToExpr k y i p sq sa spd sp
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``grammarOK) sE, mkConst ``true])
  mkAppM ``grammarOK_sound #[sE, hOK]

/-- thomQuadratic step consumption: for a root fact `⟨k, y, i, p⟩`
encoded by the step, produce the lead-resolved, coefficient-reduced
Thom region-formula fact from the root comparison — the cross-link from
opaque `rootVal` comparisons to first-order comparisons over
`evalP ρ p` and the `2Ay+B` value data. The fact is noted, rewritten
by the coefficient/lead equalities, and left in the context for the
mangle (`simp only [thomFormula]`) + `closeWithSplits`'s `findOr`-split
to consume. Skips (throws) on any missing evidence. -/
unsafe def thomStepProduce (mvar : MVarId) (ρ : Expr) (n : Nat)
    (k : RootKind) (y : Var) (i : Nat) (p : MPoly) (sq sa spd sp : Int)
    (hfvR : FVarId) : TacticM MVarId := do
  let pE := toExpr p
  let hOK ← mkDecideProof
    (← mkAppM ``Eq #[mkApp (mkConst ``MPoly.canonOK) pE, mkConst ``true])
  let hcan ← mkAppM ``MPoly.canonOK_sound #[pE, hOK]
  -- the decide ticket: all payload ranges (sq/sa/spd/sp/i/degree) are
  -- validated here (throws ⟹ step skips); semantic consumption rides
  -- `thom_discharge` below
  let _hgram ← mkThomGrammar k y i p sq sa spd sp
  let (cs, hcsPrf) ← coeffsOfValue y p
  unless cs.length == 3 do
    throwError "thomStepProduce: coefficient count {cs.length} ≠ 3"
  let c2 := cs[2]!
  let valAccs : Nat → MetaM Expr := fun k => pure (toExpr (cs[k]!))
  let zR ← mkRealZero
  -- A-sign evidence (const lane numeric; the clause lane otherwise),
  -- accessor-formed; plus a lead-resolution comparison at the value side
  let smA (accs : Nat → MetaM Expr) : MetaM Expr := do
    mkAppM ``signMatches #[toExpr sa, ← mkAppM ``Check.evalP #[ρ, ← accs 2]]
  let (hAm, hApair) ←
    if let some a := c2.asConst? then
      unless (a > 0 && sa == 1) || (a < 0 && sa == -1) do
        throwError "thomStepProduce: const A={a} inconsistent with sa={sa}"
      let c2EvE ← mkAppM ``Check.evalP #[ρ, toExpr c2]
      let cmp ←
        if a > 0 then mkAppM ``LT.lt #[zR, c2EvE]
        else mkAppM ``LT.lt #[c2EvE, zR]
      let hnum ← closeNumerically cmp
      pure (← mkValueFact hcsPrf cs smA valAccs, (decide (a > 0), hnum))
    else
      match ← findSignFact ρ c2 with
      | none => throwError "thomStepProduce: no clause sign fact for A"
      | some (sgn, hcomp, vA) =>
        unless sgn == sa do
          throwError "thomStepProduce: A sign {sgn} ≠ payload sa {sa}"
        let hVal ← mkSignMatchesOfComp sgn vA hcomp
        pure (← mkValueFactOf hcsPrf cs smA valAccs hVal, (sgn == 1, hcomp))
  -- disc-sign evidence in thom_discharge's EXPANSION form:
  -- `signMatches sq (evalP(coe[1]!)² − 4·evalP(coe[2]!)·evalP(coe[0]!))`.
  -- The clause literal is by-value against NATIVE `discPolyOf p y`
  -- (the R-ii reconstruction); the move onto the expansion's value form
  -- is the ring identity (closeAlgRefl).
  let discBody (accs : Nat → MetaM Expr) : MetaM Expr := do
    let b ← mkAppM ``Check.evalP #[ρ, ← accs 1]
    let a ← mkAppM ``Check.evalP #[ρ, ← accs 2]
    let c ← mkAppM ``Check.evalP #[ρ, ← accs 0]
    let bsq ← mkAppM ``HPow.hPow #[b, toExpr (2 : Nat)]
    let fourR ← mkAppOptM ``OfNat.ofNat
      #[some (mkConst ``Real), some (toExpr 4), none]
    let fourAC ← mkAppM ``HMul.hMul #[(← mkAppM ``HMul.hMul #[fourR, a]), c]
    let disc ← mkAppM ``HSub.hSub #[bsq, fourAC]
    mkAppM ``signMatches #[toExpr sq, disc]
  let dPoly := discPolyOf p y
  let hdm ←
    if let some dv := dPoly.asConst? then
      unless (dv > 0 && sq == 1) || (dv == 0 && sq == 0) do
        throwError "thomStepProduce: const disc={dv} inconsistent with sq={sq}"
      let hVal ← closeNumerically (← discBody valAccs)
      mkValueFactOf hcsPrf cs discBody valAccs hVal
    else
      match ← findSignFact ρ dPoly with
      | none => throwError "thomStepProduce: no clause sign fact for disc"
      | some (sgn, hcomp, vE) =>
        unless sgn == sq do
          throwError "thomStepProduce: disc sign {sgn} ≠ payload sq {sq}"
        let discVal ← do
          let b ← mkAppM ``Check.evalP #[ρ, toExpr (cs[1]!)]
          let a ← mkAppM ``Check.evalP #[ρ, toExpr c2]
          let c ← mkAppM ``Check.evalP #[ρ, toExpr (cs[0]!)]
          let bsq ← mkAppM ``HPow.hPow #[b, toExpr (2 : Nat)]
          let fourR ← mkAppOptM ``OfNat.ofNat
            #[some (mkConst ``Real), some (toExpr 4), none]
          let fourAC ← mkAppM ``HMul.hMul #[(← mkAppM ``HMul.hMul #[fourR, a]), c]
          mkAppM ``HSub.hSub #[bsq, fourAC]
        let hVE ← closeAlgRefl (← mkAppM ``Eq #[vE, discVal])
        let cmpL ← withLocalDecl `x BinderInfo.default (mkConst ``Real) fun xE => do
          mkLambdaFVars #[xE]
            (← match sgn with
               | 1 => mkAppM ``LT.lt #[zR, xE]
               | -1 => mkAppM ``LT.lt #[xE, zR]
               | _ => mkAppM ``Eq #[xE, zR])
        let hcompExp ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[cmpL, hVE]), hcomp]
        let hVal ← mkSignMatchesOfComp sgn discVal hcompExp
        mkValueFactOf hcsPrf cs discBody valAccs hVal
  -- the discharge chain: thom_discharge + rootVal_eq_quad
  let yE := toExpr y
  let hdeg2 ← mkDecideProof
    (← mkAppM ``Eq #[← mkAppM ``MPoly.degreeIn #[pE, yE], toExpr (2 : Nat)])
  let hi ← do
    let e1 ← mkAppM ``Eq #[toExpr i, toExpr (1 : Nat)]
    let e2 ← mkAppM ``Eq #[toExpr i, toExpr (2 : Nat)]
    mkDecideProof (← mkAppM ``Or #[e1, e2])
  let hsa ← mkDecideProof (← mkAppM ``Ne #[toExpr sa, toExpr (0 : Int)])
  let hsq ← do
    let e0 ← mkAppM ``Eq #[toExpr sq, toExpr (0 : Int)]
    let e1 ← mkAppM ``Eq #[toExpr sq, toExpr (1 : Int)]
    mkDecideProof (← mkAppM ``Or #[e0, e1])
  let hNev ←
    match hApair with
    | (true, hnum) => mkAppM ``ne_of_gt #[hnum]
    | (false, hnum) => mkAppM ``ne_of_lt #[hnum]
  let hAne ← mkValueFactOf hcsPrf cs (fun accs => do
      mkAppM ``Ne #[← mkAppM ``Check.evalP #[ρ, ← accs 2], zR])
    valAccs hNev
  let hcov ← mkAppM ``thom_discharge
    #[ρ, rootKindToExpr k, toExpr y, toExpr i, pE, toExpr sq, toExpr sa,
      hdeg2, hi, hcan, hsa, hAm, hsq, hdm]
  let hrveq ← mkAppM ``rootVal_eq_quad #[ρ, toExpr y, toExpr i, pE, hdeg2, hAne]
  let cmpL ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
    mkLambdaFVars #[zE]
      (mkAppN (mkConst ``rootCmp) #[rootKindToExpr k, mkApp ρ (toExpr y), zE])
  let hcmp ← mkAppM ``And.right #[mkFVar hfvR]
  let hcmpQ ← mkAppM ``Eq.mp #[(← mkAppM ``congrArg #[cmpL, hrveq]), hcmp]
  let hform ← mkAppM ``Iff.mp #[hcov, hcmpQ]
  -- coefficient reductions + lead resolution as rewrite facts:
  -- leadSgn at ACCESSOR form (rewritten first), then the two
  -- coefficient accessors
  let hC2 ← mkCoeFactEq hcsPrf cs 2 (fun v => mkAppM ``Check.evalP #[ρ, v])
  let hC1 ← mkCoeFactEq hcsPrf cs 1 (fun v => mkAppM ``Check.evalP #[ρ, v])
  let hLv ←
    match hApair with
    | (true, hnum) => mkAppM ``leadSgn_of_pos #[hnum]
    | (false, hnum) => mkAppM ``leadSgn_of_neg #[hnum]
  let hL ← mkAppM ``Eq.trans
    #[(← mkCoeFactEq hcsPrf cs 2 (fun v => do
        mkAppM ``leadSgn #[← mkAppM ``Check.evalP #[ρ, v]])),
      hLv]
  let nC2 := Name.mkSimple s!"hC2{n}"
  let nC1 := Name.mkSimple s!"hC1{n}"
  let nL := Name.mkSimple s!"hL{n}"
  let nS := Name.mkSimple s!"hS{n}"
  let (_, mv1) ← mvar.note nC2 hC2 none
  let (_, mv2) ← mv1.note nC1 hC1 none
  let (_, mv3) ← mv2.note nL hL none
  let (_, mv4) ← mv3.note nS hform none
  let saved ← getGoals
  setGoals [mv4]
  mv4.withContext do
    evalTactic (← `(tactic|
      rw [$(mkIdent nL):ident, $(mkIdent nC2):ident, $(mkIdent nC1):ident] at $(mkIdent nS):ident))
  let gnew ← getMainGoal
  setGoals saved
  pure gnew

/-- Are the `(k, i)` Thom formulas disjunctive (Or-carriers)? -/
def thomDisjunctive (k : RootKind) (i : Nat) : Bool :=
  match k, i with
  | .lt, 1 => false
  | .lt, _ => true
  | .gt, 1 => true
  | .gt, _ => false
  | .le, 1 => false
  | .le, _ => true
  | .ge, 1 => true
  | .ge, _ => false
  | .eq, _ => false

/-- Native reduct check for the sa = 0 reroute (`:811-812`): `q` is the
`B·y + C` truncation of the deg-2 parent `p` (the [1]/[0] coefficients
agree by value). -/
def reductMatch (y : Var) (p q : MPoly) : Bool :=
  let csR := p.coeffsIn y
  let csQ := q.coeffsIn y
  csR.size == 3 && csQ.size == 2 && csR[1]! == csQ[1]! && csR[0]! == csQ[0]!

/-- Step-fact collection (G4 census slice, item 3): for each encoding
step the bundle carries (preceding the `.arith` marker), match its root
atom against the extracted root facts and produce the cross-link
fact/s. Steps whose evidence is missing are skipped soundly (the
productions only ADD facts). `resolution`/`cellBound`/`factorSplit`/
`leafNumeric` steps contribute nothing (R1/R5/R6/F3). Returns the
count of potentially-Or-carrying Thom productions (matched disjunctive
`(k, i)` formulas) for the caller's split-fuel sizing. -/
unsafe def collectStepFacts (mvar : MVarId) (ρ : Expr) (steps : Array TraceStep)
    (rootFacts : Array (RootKind × Var × Nat × MPoly × FVarId)) :
    TacticM (MVarId × Nat) := do
  let mut mvar := mvar
  let mut n : Nat := 0
  -- encoding-free lane (foreign traces): every deg-1 root fact with a
  -- const lc converts via rootVal_eq_linear without any step
  for (k, y, i, p, hfvR) in rootFacts do
    if p.degreeIn y == 1 && i == 1 then
      mvar ← mvar.withContext do
        try
          rootGenericLinearProduce mvar ρ n k y i p hfvR
        catch _ =>
          pure mvar
      n := n + 1
  for step in steps do
    match step with
    | .linearRoot k y q mkNeg lcFact => do
      let matched := rootFacts.filter fun (kR, yR, _, pR, _) =>
        kR == k && yR == y && pR == q
      for (_, _, iR, _, hfvR) in matched do
        mvar ← mvar.withContext do
          try
            linearStepProduce mvar ρ n k y iR q mkNeg lcFact hfvR
          catch _ =>
            pure mvar
        n := n + 1
      -- the sa = 0 degenerate reroute (mk_quadratic_root :811-812): the
      -- linearRoot step is on the reduct of a deg-2 parent
      let reducts := rootFacts.filter fun (kR, yR, _, pR, _) =>
        kR == k && yR == y && pR.degreeIn yR == 2 && reductMatch yR pR q
      for (_, _, iR, pR, hfvR) in reducts do
        mvar ← mvar.withContext do
          try
            linearStepProduceDeg mvar ρ n k y iR pR q mkNeg lcFact hfvR
          catch _ =>
            pure mvar
        n := n + 1
    | .thomQuadratic k y i p sq sa spd sp => do
      let matched := rootFacts.filter fun (kR, yR, iR, pR, _) =>
        kR == k && yR == y && iR == i && pR == p
      for (_, _, _, _, hfvR) in matched do
        mvar ← mvar.withContext do
          try
            thomStepProduce mvar ρ n k y i p sq sa spd sp hfvR
          catch _ =>
            pure mvar
        n := n + 1
    -- G11: the production rootGeneric lane (deg-1, non-const lc —
    -- matched by (k, y, i, p); other degrees/kinds have no lane)
    | .rootGeneric k y i p => do
      let matched := rootFacts.filter fun (kR, yR, iR, pR, _) =>
        kR == k && yR == y && iR == i && pR == p
      for (_, _, _, _, hfvR) in matched do
        mvar ← mvar.withContext do
          try
            rootGenericStepProduce mvar ρ n k y i p hfvR
          catch _ =>
            pure mvar
        n := n + 1
    | _ => pure ()
  pure (mvar, steps.foldl (fun acc s =>
    match s with
    | .thomQuadratic k y i p _ _ _ _ =>
      if thomDisjunctive k i &&
         (rootFacts.any fun (kR, yR, iR, pR, _) =>
           kR == k && yR == y && iR == i && pR == p) then acc + 1 else acc
    | _ => acc) 0)

/-- Native view of a `pseudoDivision` step payload. -/
structure PdStepV where
  f : MPoly
  eq : MPoly
  x : Var
  d : Nat
  r : MPoly
  lcSign : Int
  isEven : Bool
deriving BEq

/-- The step's leading coefficient `(eq.coeffsIn x)[degreeIn x]!`
(z3's `coeff(eq, x, k)`, :1228-1231). -/
def PdStepV.lc (st : PdStepV) : MPoly :=
  (st.eq.coeffsIn st.x)[st.eq.degreeIn st.x]!

/-- Quote an `IneqKind` (no `ToExpr` instance — ctor applications). -/
def ineqKindToExpr : IneqKind → Expr
  | .eq => mkConst ``IneqKind.eq
  | .lt => mkConst ``IneqKind.lt
  | .gt => mkConst ``IneqKind.gt

/-- `(1 : ℝ)`. -/
def mkRealOne : MetaM Expr :=
  mkAppOptM ``OfNat.ofNat #[some (mkConst ``Real), some (toExpr 1), none]

/-- `(-1 : ℝ)`. -/
def mkRealNegOne : MetaM Expr := do mkAppM ``Neg.neg #[← mkRealOne]

/-- Close `oddSigProd σs fs = 1` / `= -1` over concrete ±1-literal
lists: unfold + norm_num. Sandbox-managed with the `hasMVar` hole
discipline (19b Slice 1, the closeAlgRefl trap). -/
def closeSigProd (tgt : Expr) : TacticM Expr := do
  let saved ← getGoals
  try
    let h ← withoutModifyingState do
      let m ← mkFreshExprMVar tgt
      setGoals [m.mvarId!]
      m.mvarId!.withContext do
        evalTactic (← `(tactic| simp only [oddSigProd]))
        evalTactic (← `(tactic| norm_num))
      let h ← instantiateMVars m
      if h.hasMVar then
        throwError "closeSigProd: subgoal not closed"
      pure h
    setGoals saved
    pure h
  catch e =>
    setGoals saved
    throw e

/-- The pd lane's threaded state: the goal mvar, the fact indexes, and
the per-step identity cache. (Explicit state record — `withContext`
closures can't assign captured `let mut`s.) -/
structure PdState where
  mvar : MVarId
  eqFacts : Array (MPoly × FVarId)
  diseqFacts : Array (MPoly × FVarId)
  signPosFacts : Array (IneqKind × MPoly × FVarId)
  prodEqFacts : Array (List (MPoly × Bool) × FVarId)
  chainFacts : Array (FVarId × List (MPoly × Bool))
  idCache : Array (PdStepV × MPoly × Expr)

/-- 19b Slice 2 — the pseudoDivision consumption lane (the R7 gap).

z3's `simplify(literal, …)` (nlsat_explain.cpp:1096-1216, read against
`git show z3-4.12.5:`) rewrites core literals against the selected
equation factor-by-factor, emitting one `pseudoDivision` step per
replaced factor. The clause only ever shows the REBUILT atom; the
original literal appears nowhere. This lane closes the gap:

**Transport lane** (per clause literal): match the rebuilt atom's
factor list against the steps' remainders BY VALUE (the F2-seam
discipline); unmatched positions are the kept factors (z3 keeps
`degree < k` factors verbatim, :1124-1128). Per matched position
re-prove the pseudo-division identity (`pseudoDivisionIdentity`,
Slice 1), take `lc ≠ 0` from the clause's own A5 diseq literal (or
decide-grade for a const lc), and — only where z3's own assumption
structure provides it — the lc's SIGN from the A4 literal
(`add_lc_ineq` fires exactly when d odd ∧ factor odd ∧ kind ≠ EQ,
:1176-1184). The per-position evidence assembles into `SignRel`
(lt/gt kinds) / `ZeroRel` (eq kind — z3 never needs the lc sign
there), the literal's `Holds` transports across `holds_signRel` /
`holds_zeroRel_eq` to the reconstructed ORIGINAL factor list, and the
standard `extractPosFacts`/`extractNegFacts` runs on it — the noted
facts feed the eq/diseq/prod/chain indexes and the existing closes
consume them uniformly. The kind-flip count is the native σ-product
(z3's running `atom_sign`, :1113/:1136/:1171); the `hk` hypothesis is
discharged against the concrete σ list, so a miscount fails to
elaborate rather than producing a wrong fact.

**Drop lane** (per step with a CONST remainder, :1149-1185): the
position vanishes from the rebuilt literal (or collapses it
entirely), so nothing matches by value. The content is a definite
fact on the original factor, gated on the clause carrying the eq
fact: remainder 0 ⟹ `f = 0` (the path-(b) collapse :1149-1162);
nonzero const ⟹ `f ≠ 0` always (lc ≠ 0 suffices) plus the definite
sign when the lc evidence determines it (d even ⟹ `sign f = sign r`;
d odd ⟹ `lc-sign · sign r`).

Completeness argument (genuine z3 emissions always close): a replaced
odd position of an lt/gt atom with d odd carries the A4 sign literal
by z3's own assumption rule (:1181-1184); everything else needs only
the A5 diseq or a const lc. Foreign/corrupt payloads throw at the
identity or the evidence lookup and skip soundly (participation, not
trust). Unmatched steps (path (c) keep-original, :1197-1200)
contribute nothing. -/
unsafe def pdRewriteLane (mvar : MVarId) (ρ IE : Expr) (steps : Array TraceStep)
    (litAtoms : Array (Literal × Atom × FVarId))
    (eqFacts diseqFacts : Array (MPoly × FVarId))
    (signPosFacts : Array (IneqKind × MPoly × FVarId))
    (prodEqFacts : Array (List (MPoly × Bool) × FVarId))
    (chainFacts : Array (FVarId × List (MPoly × Bool))) :
    TacticM (MVarId × Array (MPoly × FVarId) × Array (MPoly × FVarId) ×
      Array (IneqKind × MPoly × FVarId) × Array (List (MPoly × Bool) × FVarId) ×
      Array (FVarId × List (MPoly × Bool))) := do
  let pds : Array PdStepV := steps.filterMap fun
    | .pseudoDivision f eq x d r lcSign isEven => some ⟨f, eq, x, d, r, lcSign, isEven⟩
    | _ => none
  if pds.isEmpty then
    return (mvar, eqFacts, diseqFacts, signPosFacts, prodEqFacts, chainFacts)
  -- per-step identity, cached (throws on a corrupt payload — the
  -- caller's catch skips soundly)
  let getId (S : PdState) (st : PdStepV) : TacticM (PdState × MPoly × Expr) := do
    match S.idCache.find? (·.1 == st) with
    | some (_, lc, hId) => pure (S, lc, hId)
    | none =>
      let (lc, hId) ← pseudoDivisionIdentity ρ st.f st.eq st.x st.d st.r
      pure ({ S with idCache := S.idCache.push (st, lc, hId) }, lc, hId)
  -- `lc ≠ 0` evidence: decide-grade for a const lc, else the clause's
  -- A5 diseq literal, else from an A4 sign fact
  let lcNeOf (S : PdState) (lc : MPoly) : TacticM Expr := do
    match lc.asConst? with
    | some v =>
      if v == 0 then
        throwError "pdRewrite: const-zero lc (impossible for a canonical lc)"
      else
        closeNumerically (← mkAppM ``Ne
          #[← mkAppM ``Check.evalP #[ρ, toExpr lc], ← mkRealZero])
    | none =>
      match S.diseqFacts.find? (·.1 == lc) with
      | some (_, fv) => pure (mkFVar fv)
      | none =>
        match S.signPosFacts.find? (fun (_, q, _) => q == lc) with
        | some (.gt, _, fv) => mkAppM ``ne_of_gt #[mkFVar fv]
        | some (.lt, _, fv) => mkAppM ``ne_of_lt #[mkFVar fv]
        | _ => throwError "pdRewrite: no lc ≠ 0 evidence in the clause"
  -- the lc's sign: `some (true, h)` = `0 < lc`, `some (false, h)` =
  -- `lc < 0`; decide-grade for a const lc, else the A4 literal
  let lcSignOf (S : PdState) (lc : MPoly) : TacticM (Option (Bool × Expr)) := do
    match lc.asConst? with
    | some v =>
      if v > 0 then
        try
          pure (some (true, ← closeNumerically (← mkAppM ``LT.lt
            #[← mkRealZero, ← mkAppM ``Check.evalP #[ρ, toExpr lc]])))
        catch _ => pure none
      else if v < 0 then
        try
          pure (some (false, ← closeNumerically (← mkAppM ``LT.lt
            #[← mkAppM ``Check.evalP #[ρ, toExpr lc], ← mkRealZero])))
        catch _ => pure none
      else pure none
    | none =>
      match S.signPosFacts.find? (fun (k, q, _) => k == .gt && q == lc) with
      | some (_, _, fv) => pure (some (true, mkFVar fv))
      | none =>
        match S.signPosFacts.find? (fun (k, q, _) => k == .lt && q == lc) with
        | some (_, _, fv) => pure (some (false, mkFVar fv))
        | none => pure none
  -- hId with the exponent respelled `2 * (d/2)` / `2 * (d/2) + 1` —
  -- the Slice-1 family's hypothesis shapes. Eq.mp is FORWARD along
  -- `motive d = motive target` (the Eq.mpr-is-backward trap).
  let normalizeExp (st : PdStepV) (lc q : MPoly) (hId : Expr) : TacticM Expr := do
    let m := st.d / 2
    let target := if st.d % 2 == 0 then 2 * m else 2 * m + 1
    let hDE ← mkDecideProof (← mkAppM ``Eq #[toExpr st.d, toExpr target])
    let lcValE ← mkAppM ``Check.evalP #[ρ, toExpr lc]
    let fValE ← mkAppM ``Check.evalP #[ρ, toExpr st.f]
    let qValE ← mkAppM ``Check.evalP #[ρ, toExpr q]
    let eqValE ← mkAppM ``Check.evalP #[ρ, toExpr st.eq]
    let rValE ← mkAppM ``Check.evalP #[ρ, toExpr st.r]
    let motiveE ← withLocalDecl `e BinderInfo.default (mkConst ``Nat) fun eE => do
      let powE ← mkAppM ``HPow.hPow #[lcValE, eE]
      let lhsE ← mkAppM ``HMul.hMul #[powE, fValE]
      let rhsE ← mkAppM ``HAdd.hAdd
        #[(← mkAppM ``HMul.hMul #[qValE, eqValE]), rValE]
      mkLambdaFVars #[eE] (← mkAppM ``Eq #[lhsE, rhsE])
    let hCongr ← mkAppM ``congrArg #[motiveE, hDE]
    mkAppM ``Eq.mp #[hCongr, hId]
  -- the Slice-1 family application, all implicits pinned (the `2 * m`
  -- exponent form does not unify against the literal exponent with `m`
  -- free)
  let appPd (nm : Name) (st : PdStepV) (lc q : MPoly) (hL hE hIdP : Expr) :
      TacticM Expr := do
    let lcValE ← mkAppM ``Check.evalP #[ρ, toExpr lc]
    let fValE ← mkAppM ``Check.evalP #[ρ, toExpr st.f]
    let qValE ← mkAppM ``Check.evalP #[ρ, toExpr q]
    let eqValE ← mkAppM ``Check.evalP #[ρ, toExpr st.eq]
    let rValE ← mkAppM ``Check.evalP #[ρ, toExpr st.r]
    mkAppOptM nm #[some lcValE, some fValE, some qValE, some eqValE, some rValE,
      some (toExpr (st.d / 2)), some hL, some hE, some hIdP]
  -- (σ, pack proof `Real.sign F = σ · Real.sign R`) for a replaced ODD
  -- position of an lt/gt atom; throws when the lc-sign evidence is
  -- missing (z3's A4/A5 rule :1176-1184 guarantees it for genuine
  -- emissions)
  let packOf (S : PdState) (st : PdStepV) (lc : MPoly) (hLne hE hId hz : Expr) :
      TacticM (Int × Expr) := do
    let (_, q, _) := MPoly.pseudoDivisionCore st.f st.eq st.x false true
    let hIdP ← normalizeExp st lc q hId
    if st.d % 2 == 0 then
      let hgt ← appPd ``pdSign_even_gt st lc q hLne hE hIdP
      let hlt ← appPd ``pdSign_even_lt st lc q hLne hE hIdP
      pure (1, ← mkAppM ``pdSign_pack_pos #[hz, hgt, hlt])
    else
      match ← lcSignOf S lc with
      | some (true, hLpos) =>
        let hgt ← appPd ``pdSign_odd_pos_gt st lc q hLpos hE hIdP
        let hlt ← appPd ``pdSign_odd_pos_lt st lc q hLpos hE hIdP
        pure (1, ← mkAppM ``pdSign_pack_pos #[hz, hgt, hlt])
      | some (false, hLneg) =>
        let hgt ← appPd ``pdSign_odd_neg_gt st lc q hLneg hE hIdP
        let hlt ← appPd ``pdSign_odd_neg_lt st lc q hLneg hE hIdP
        pure (-1, ← mkAppM ``pdSign_pack_neg #[hz, hgt, hlt])
      | none => throwError "pdRewrite: no lc-sign evidence for an odd-d position"
  -- note the transported extraction facts, updating the indexes
  let noteFacts (S : PdState) (facts : List (Expr × FactKind)) : TacticM PdState := do
    let mut S := S
    for (fact, kind) in facts do
      let (hfv, mv) ← S.mvar.note `h_f fact none
      S := { S with mvar := mv }
      match kind with
      | .eqZero q => S := { S with eqFacts := S.eqFacts.push (q, hfv) }
      | .neZero q => S := { S with diseqFacts := S.diseqFacts.push (q, hfv) }
      | .eqProdZero fs => S := { S with prodEqFacts := S.prodEqFacts.push (fs, hfv) }
      | .negChain fs => S := { S with chainFacts := S.chainFacts.push (hfv, fs) }
      | .signPos kk q => S := { S with signPosFacts := S.signPosFacts.push (kk, q, hfv) }
      | _ => pure ()
    pure S
  -- **Drop lane** (const remainders; runs FIRST so its definite facts
  -- can serve as lc evidence for the transports)
  let dropStep (S : PdState) (st : PdStepV) : TacticM PdState := do
    let some v := st.r.asConst? | pure S
    S.mvar.withContext do
      try
        let mut S := S
        let some (_, hEFv) := S.eqFacts.find? (·.1 == st.eq)
          | throwError "pdRewrite: no eq fact for a const-r step"
        let lc := st.lc
        let hLne ← lcNeOf S lc
        let (S', _, hId) ← getId S st
        S := S'
        let hz ← mkAppM ``pdSign_eq #[hLne, mkFVar hEFv, hId]
        let rValE ← mkAppM ``Check.evalP #[ρ, toExpr st.r]
        if v == 0 then
          -- path (b) collapse (:1149-1162): the factor vanishes
          let hR0 ← closeNumerically (← mkAppM ``Eq #[rValE, ← mkRealZero])
          let hf0 ← mkAppM ``Iff.mpr #[hz, hR0]
          let (hfv, mv) ← S.mvar.note `h_f hf0 none
          S := { S with mvar := mv, eqFacts := S.eqFacts.push (st.f, hfv) }
        else
          let hRne ← closeNumerically (← mkAppM ``Ne #[rValE, ← mkRealZero])
          let hfNe ← mkAppM ``mt #[(← mkAppM ``Iff.mp #[hz]), hRne]
          let (hfv, mv) ← S.mvar.note `h_f hfNe none
          S := { S with mvar := mv, diseqFacts := S.diseqFacts.push (st.f, hfv) }
          -- the definite sign, when the evidence determines it
          try
            let (_, q, _) := MPoly.pseudoDivisionCore st.f st.eq st.x false true
            let hIdP ← normalizeExp st lc q hId
            let (gtNm, ltNm, hL, flip) ←
              if st.d % 2 == 0 then
                pure (``pdSign_even_gt, ``pdSign_even_lt, hLne, false)
              else
                match ← lcSignOf S lc with
                | some (true, hLpos) =>
                  pure (``pdSign_odd_pos_gt, ``pdSign_odd_pos_lt, hLpos, false)
                | some (false, hLneg) =>
                  pure (``pdSign_odd_neg_gt, ``pdSign_odd_neg_lt, hLneg, true)
                | none => throwError "pdRewrite: no lc-sign evidence"
            -- family pos: `0<F ↔ 0<R` / `F<0 ↔ R<0`; neg: flipped
            let (sgn, hf) ←
              if v > 0 then
                let hRpos ← closeNumerically
                  (← mkAppM ``LT.lt #[← mkRealZero, rValE])
                if !flip then
                  pure (IneqKind.gt, ← mkAppM ``Iff.mpr
                    #[(← appPd gtNm st lc q hL (mkFVar hEFv) hIdP), hRpos])
                else
                  pure (IneqKind.lt, ← mkAppM ``Iff.mpr
                    #[(← appPd ltNm st lc q hL (mkFVar hEFv) hIdP), hRpos])
              else
                let hRneg ← closeNumerically
                  (← mkAppM ``LT.lt #[rValE, ← mkRealZero])
                if !flip then
                  pure (IneqKind.lt, ← mkAppM ``Iff.mpr
                    #[(← appPd ltNm st lc q hL (mkFVar hEFv) hIdP), hRneg])
                else
                  pure (IneqKind.gt, ← mkAppM ``Iff.mpr
                    #[(← appPd gtNm st lc q hL (mkFVar hEFv) hIdP), hRneg])
            let (hfv, mv) ← S.mvar.note `h_f hf none
            S := { S with mvar := mv, signPosFacts := S.signPosFacts.push (sgn, st.f, hfv) }
            pure ()
          catch _ => pure ()
        pure S
      catch _ => pure S
  -- **Transport lane**
  let transportLit (S : PdState) (l : Literal) (k' : IneqKind)
      (fs_r : List (MPoly × Bool)) (h_iFv : FVarId) : TacticM PdState := do
    S.mvar.withContext do
      try
        -- match the rebuilt atom's positions against the steps'
        -- remainders by value; build the per-position evidence
        let mut S := S
        let mut positions :
            Array (MPoly × MPoly × Bool × Expr × Option (Int × Expr)) := #[]
        let mut anyMatch := false
        for (rp, mo) in fs_r do
          match pds.find? fun st => st.r == rp with
          | none =>
            -- kept factor (:1124-1128): fp = rp, σ = 1
            let rpValE ← mkAppM ``Check.evalP #[ρ, toExpr rp]
            let hz ← mkAppM ``Iff.refl #[← mkAppM ``Eq #[rpValE, ← mkRealZero]]
            let hs? ← if mo || k' == .eq then pure none else
              pure (some (1, ← mkAppM ``Eq.symm
                #[← mkAppM ``one_mul #[← mkAppM ``Real.sign #[rpValE]]]))
            positions := positions.push (rp, rp, mo, hz, hs?)
          | some st =>
            anyMatch := true
            let some (_, hEFv) := S.eqFacts.find? (·.1 == st.eq)
              | throwError "pdRewrite: no eq fact for a matched step"
            let lc := st.lc
            let hLne ← lcNeOf S lc
            let (S', _, hId) ← getId S st
            S := S'
            let hz ← mkAppM ``pdSign_eq #[hLne, mkFVar hEFv, hId]
            let hs? ← if mo || k' == .eq then pure none else do
              let (σ, hsP) ← packOf S st lc hLne (mkFVar hEFv) hId hz
              pure (some (σ, hsP))
            positions := positions.push (st.f, rp, mo, hz, hs?)
        unless anyMatch do
          throwError "pdRewrite: not a rebuilt literal"
        let fs_oN : List (MPoly × Bool) :=
          positions.toList.map fun (fp, _, mo, _, _) => (fp, mo)
        -- the original kind: flip iff the odd-position σ-product is
        -- −1 (z3's `atom_sign < 0 → flip`, :1191-1193)
        let sigProdI : Int := positions.foldl (fun acc (_, _, mo, _, hs?) =>
          if mo then acc else match hs? with | some (σ, _) => acc * σ | none => acc) 1
        let k := if sigProdI == -1 then k'.flip else k'
        -- the transport Iff
        let hIff ←
          if k' == .eq then
            -- ZeroRel: zero-status only — z3 adds just `add_lc_diseq`
            -- for EQ (:1181-1184); `atom::flip EQ = EQ`
            let mut relPrf ← mkAppOptM ``ZeroRel.nil #[some ρ]
            for (fp, rp, mo, hz, _) in positions.reverse do
              relPrf ← mkAppM ``ZeroRel.cons
                #[toExpr fp, toExpr rp, toExpr mo, hz, relPrf]
            mkAppM ``holds_zeroRel_eq #[ρ, toExpr fs_oN, toExpr fs_r, relPrf]
          else
            let mut relPrf ← mkAppOptM ``SignRel.nil #[some ρ]
            let mut σsE ← mkAppOptM ``List.nil #[some (mkConst ``Real)]
            for (fp, rp, _, hz, hs?) in positions.reverse do
              match hs? with
              | some (σ, hsP) =>
                let sE ← if σ == 1 then mkRealOne else mkRealNegOne
                let oneE ← mkRealOne
                let negOneE ← mkRealNegOne
                let hs1 ← if σ == 1 then
                  mkAppOptM ``Or.inl #[none,
                    some (← mkAppM ``Eq #[sE, negOneE]),
                    some (← mkAppM ``Eq.refl #[sE])]
                else
                  mkAppOptM ``Or.inr #[some (← mkAppM ``Eq #[sE, oneE]),
                    none, some (← mkAppM ``Eq.refl #[sE])]
                relPrf ← mkAppM ``SignRel.consOdd
                  #[sE, toExpr fp, toExpr rp, hz, hsP, hs1, relPrf]
                σsE ← mkAppM ``List.cons #[sE, σsE]
              | none =>
                relPrf ← mkAppM ``SignRel.consEven #[toExpr fp, toExpr rp, hz, relPrf]
                σsE ← mkAppM ``List.cons #[(← mkRealOne), σsE]
            let ospE ← mkAppM ``oddSigProd #[σsE, toExpr fs_oN]
            let oneE ← mkRealOne
            let negOneE ← mkRealNegOne
            let kE := ineqKindToExpr k
            let k'E := ineqKindToExpr k'
            let kFlipE := ineqKindToExpr k'.flip
            let hS ← closeSigProd (← mkAppM ``Eq
              #[ospE, (if sigProdI == 1 then oneE else negOneE)])
            let hkk ← mkAppM ``Eq.refl #[kE]
            let hAnd ← mkAppM ``And.intro #[hS, hkk]
            let leftTy ← mkAppM ``And
              #[← mkAppM ``Eq #[ospE, oneE], ← mkAppM ``Eq #[kE, k'E]]
            let rightTy ← mkAppM ``And
              #[← mkAppM ``Eq #[ospE, negOneE], ← mkAppM ``Eq #[kE, kFlipE]]
            let hk ← if sigProdI == 1 then
              mkAppOptM ``Or.inl #[none, some rightTy, some hAnd]
            else
              mkAppOptM ``Or.inr #[some leftTy, none, some hAnd]
            mkAppM ``holds_signRel
              #[ρ, kE, k'E, σsE, toExpr fs_oN, toExpr fs_r, relPrf, hk]
        -- transport the literal's fact across, re-extract on the
        -- original factor list, note + index
        let aE := mkApp IE (toExpr l.bvar)
        if l.neg then
          let nn ← mkAppOptM ``Classical.not_not #[some aE]
          let hH_r ← mkAppM ``Iff.mp #[nn, mkFVar h_iFv]
          let hH_o ← mkAppM ``Iff.mpr #[hIff, hH_r]
          noteFacts S (← extractPosFacts ρ (.ineq ⟨k, fs_oN⟩) hH_o)
        else
          let hNH_o ← mkAppM ``mt #[(← mkAppM ``Iff.mp #[hIff]), mkFVar h_iFv]
          noteFacts S (← extractNegFacts ρ (.ineq ⟨k, fs_oN⟩) hNH_o)
      catch _ => pure S
  let mut S : PdState :=
    ⟨mvar, eqFacts, diseqFacts, signPosFacts, prodEqFacts, chainFacts, #[]⟩
  for st in pds do
    S ← dropStep S st
  for (l, a, h_iFv) in litAtoms do
    match a with
    | .ineq ⟨k', fs_r⟩ => S ← transportLit S l k' fs_r h_iFv
    | .root _ => continue
  pure (S.mvar, S.eqFacts, S.diseqFacts, S.signPosFacts, S.prodEqFacts, S.chainFacts)

/-- Core worker: prove `clauseSatI (interp ρ atoms) C` for concrete
`atoms`, `C`. `hName` seeds the extracted-fact names. Failure (any
undecodable literal, skipped shape, or glue failure) propagates as a
tactic error — the sound direction. `unsafe` for the native decode
(`Meta.evalExpr`) — untrusted meta, the produced terms are
kernel-checked. `steps` is the bundle's projection-step context
(G4 census item 3 — step-fact collection; `#[]` outside the walk). -/
unsafe def proveClauseSat (mvar : MVarId) (steps : Array TraceStep := #[]) :
    TacticM Unit := do
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
  let mut rootFacts : Array (RootKind × Var × Nat × MPoly × FVarId) := #[]
  -- G11: positive-polarity root literals (the `¬ Holds` side)
  let mut negRootFacts : Array (RootKind × Var × Nat × MPoly × FVarId) := #[]
  -- 19b Slice 2: the positive single-factor comparisons (the A4
  -- lc-sign evidence index for the pseudoDivision lane)
  let mut signPosFacts : Array (IneqKind × MPoly × FVarId) := #[]
  -- 19b Slice 2: (literal, atom, h_i fvar) per ineq literal — the pd
  -- lane's transport inputs
  let mut litAtoms : Array (Literal × Atom × FVarId) := #[]
  for l in CV do
    -- everything that typechecks terms mentioning context fvars must
    -- run in the CURRENT mvar's local context (hFvar, noted facts)
    let (mvar', wasSkipped, factInfo, h_iFvar?) ← mvar.withContext do
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
          | [] => pure (mvar1, true, ((#[], #[], #[], #[], #[], #[], #[]) :
              Array (MPoly × FVarId) × Array (MPoly × FVarId) ×
              Array (List (MPoly × Bool) × FVarId) ×
              Array (FVarId × List (MPoly × Bool)) ×
              Array (RootKind × Var × Nat × MPoly × FVarId) ×
              Array (RootKind × Var × Nat × MPoly × FVarId) ×
              Array (IneqKind × MPoly × FVarId)), some h_iFvar)
          | facts =>
            let mut mv := mvar1
            let mut eqs : Array (MPoly × FVarId) := #[]
            let mut neqs : Array (MPoly × FVarId) := #[]
            let mut prods : Array (List (MPoly × Bool) × FVarId) := #[]
            let mut chs : Array (FVarId × List (MPoly × Bool)) := #[]
            let mut roots : Array (RootKind × Var × Nat × MPoly × FVarId) := #[]
            let mut nroots : Array (RootKind × Var × Nat × MPoly × FVarId) := #[]
            let mut spos : Array (IneqKind × MPoly × FVarId) := #[]
            for (fact, kind) in facts do
              let (hfv, mv') ← mv.note `h_f fact none
              mv := mv'
              match kind with
              | .eqZero q => eqs := eqs.push (q, hfv)
              | .neZero q => neqs := neqs.push (q, hfv)
              | .eqProdZero fs => prods := prods.push (fs, hfv)
              | .negChain fs => chs := chs.push (hfv, fs)
              | .rootPair k y i p => roots := roots.push (k, y, i, p, hfv)
              | .negRoot k y i p => nroots := nroots.push (k, y, i, p, hfv)
              | .signPos k q => spos := spos.push (k, q, hfv)
              | .other => pure ()
            pure (mv, false, (eqs, neqs, prods, chs, roots, nroots, spos),
              some h_iFvar)
      | _ =>
        throwError "nlsat_arith_valid: literal {repr l} is undecodable in the atom table"
    mvar := mvar'
    if wasSkipped then skipped := skipped.push l
    match atomsV[l.bvar]?, h_iFvar? with
    | some (some a), some h_iFvar =>
      vars := vars ++ atomVars a
      -- the pd lane's per-literal transport inputs (root atoms are
      -- never rebuilt — z3 `simplify` returns them unmodified,
      -- nlsat_explain.cpp:1100-1103)
      match a with
      | .ineq _ => litAtoms := litAtoms.push (l, a, h_iFvar)
      | .root _ => pure ()
    | some (some a), none => vars := vars ++ atomVars a
    | _, _ => pure ()
    eqFacts := eqFacts ++ factInfo.1
    diseqFacts := diseqFacts ++ factInfo.2.1
    prodEqFacts := prodEqFacts ++ factInfo.2.2.1
    chainFacts := chainFacts ++ factInfo.2.2.2.1
    rootFacts := rootFacts ++ factInfo.2.2.2.2.1
    negRootFacts := negRootFacts ++ factInfo.2.2.2.2.2.1
    signPosFacts := signPosFacts ++ factInfo.2.2.2.2.2.2
  -- "eq × bare-variable" lift (the o139 cid-8 lesson): nlinarith only
  -- pairs HYPOTHESES — it cannot multiply an equality by a free
  -- variable. CAD-derived contradictions routinely need exactly that
  -- (multiply `y0·y4 = y1·y3` by y2 to route a strict inequality
  -- through it). Noting the var-scaled variants directly as hypotheses
  -- makes them available to the linear+pair-product cone. Sound via
  -- congrArg + `zero_mul`.
  let mut scaleCounter := 0
  for (_, hfv) in eqFacts do
    for v in vars.eraseDup do
      let vv := mkApp ρ (toExpr v)
      let mvar' ← mvar.withContext do
        let lam ← withLocalDecl `z BinderInfo.default (mkConst ``Real) fun zE => do
          mkLambdaFVars #[zE] (← mkAppM ``HMul.hMul #[zE, vv])
        let t ← mkAppM ``congrArg #[lam, mkFVar hfv]
        let h0 ← mkAppM ``zero_mul #[vv]
        let scaled ← mkAppM ``Eq.trans #[t, h0]
        let (_, mv) ← mvar.note (Name.mkSimple s!"hXS{scaleCounter}") scaled none
        pure mv
      mvar := mvar'
      scaleCounter := scaleCounter + 1
  -- sq_nonneg hints per occurring variable (nlinarith's nonlinear leaf)
  for v in vars.eraseDup do
    mvar ← mvar.withContext do
      let sqn ← mkAppM ``sq_nonneg #[mkApp ρ (toExpr v)]
      let (_, mvar') ← mvar.note `h_sq sqn none
      pure mvar'
  -- G4 census item 3: step-fact collection (the cross-links census
  -- member). The bundle's encoding steps convert the extracted root
  -- facts' opaque `rootVal` comparisons into glue-ready first-order
  -- facts. Productions only ADD facts; missing evidence skips soundly.
  -- (Runs even with no steps: the encoding-free lane handles foreign
  -- deg-1 root facts.)
  let (mvarC, thomOrs) ← collectStepFacts mvar ρ steps rootFacts
  mvar := mvarC
  -- 19b Slice 2: pseudoDivision consumption — the rebuilt-literal
  -- transport + const-remainder drop lane. Runs after the fact indexes
  -- are collected (it reads them) and before the closes (it feeds
  -- them).
  let (mvarP, eqF, neqF, _sposF, prodF, chainF) ←
    pdRewriteLane mvar ρ IE steps litAtoms eqFacts diseqFacts signPosFacts
      prodEqFacts chainFacts
  mvar := mvarP
  eqFacts := eqF; diseqFacts := neqF; prodEqFacts := prodF; chainFacts := chainF
  -- G11 negative side: positive-in-clause root literals (deg-1 lane;
  -- step-independent semantic conversion). Produces the
  -- `negHolds_deg1_disjunction` splits. Misses skip soundly.
  let mut n : Nat := 0
  for (k, y, i, p, hfvN) in negRootFacts do
    mvar ← mvar.withContext do
      try negRootDeg1Produce mvar ρ n k y i p hfvN
      catch _ => pure mvar
    n := n + 1
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
        thomFormula, rootCmp,
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
  -- literal + margin covers every split the loop can make. The item-3
  -- Thom formula facts add up to `thomOrs` independent Or carriers;
  -- each Or's split doubles the branch tree, so the clause-based
  -- budget is multiplied by 2^thomOrs (G4 census item 3). 19b Slice 2:
  -- the pd lane's transports preserve the factor count per literal
  -- (drops are never inserted into the rebuilt list), so transported
  -- diseq facts stay inside the per-literal bound; the drop lane adds
  -- ≤ 2 indexed facts per pseudoDivision STEP, so the budget gains
  -- 2·|pdSteps| (bundle-sized, not a hardcoded constant).
  let fuel := (CV.foldl (fun acc l =>
    match atomsV[l.bvar]? with
    | some (some (.ineq a)) => acc + 2 * (a.factors.length + 1)
    | _ => acc + 2) 0 + 4 +
    2 * (steps.filter (fun | .pseudoDivision .. => true | _ => false)).size)
    * 2 ^ thomOrs
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

/-- `nlsat_arith_valid_steps s` — as `nlsat_arith_valid`, with the
bundle's projection steps `s : Array TraceStep` consumed by step-fact
collection (the G4 cross-links census member). -/
elab "nlsat_arith_valid_steps " s:term : tactic => unsafe (do
  let stepsTyE ← Term.elabType (← `(Array TraceStep))
  let sE ← Term.elabTerm s (some stepsTyE)
  let stepsV ← Meta.evalExpr (Array TraceStep) stepsTyE sE
  proveClauseSat (← getMainGoal) stepsV)

end Refute
end LeanNonlinearArith.Nlsat
