import LeanNonlinearArith.Nlsat.Walk
import LeanNonlinearArith.Nlsat.Quote
import LeanNonlinearArith.Nlsat.Explain
import LeanNonlinearArith.Tactic.Saturate

/-!
# nla-14 Slice 2 — reify + Tseitin + bridge (the `nonlinear_arith` frontend core)

Transforms an arithmetic goal into the walk's refutation goal. Phases:

1. **Reify** (`reifyProp`): the goal's non-dependent prop hyps + the
   negated goal are parsed into `BoolDef` trees over solver literals.
   Arithmetic terms map to `MPoly` over a variable table (ℤ vars →
   integrality-hyp slots, ℕ vars → ℤ + a `0 ≤ ↑n` unit clause, ℝ vars
   direct, opaque non-polynomial subterms → fresh variables — z3's
   uninterpreted-content treatment; div/mod hard-fail — the L1
   invariant, §2.7). Comparisons fold to one atom per (kind,
   difference-poly), polarity in the literal's `neg` bit.
2. **Tseitin** (`clausify`/`tseitinLit`): NNF + proxies for nested
   structure (`mkBoolVar`-shaped slots carrying `.bool` defs —
   hierarchical, design-review R-i/R-ii), producing definitional
   clauses (taut-discharged, children abstract) and root clauses
   (hyp-side bridges by ∃-introduction through the elimination plan).
3. **Bridge** (term-mode, no trust): per-literal chains
   (`holds_single_*` + the evalP-homomorphism alignment + cast Iffs),
   per-proxy chains (`litHolds_bool` + `boolDefHolds_evalLitHolds`),
   definitional clauses via `taut_sound` + `clauseHolds_iff_eval`,
   and the final `∀ C ∈ Cs, clauseHolds ρ atoms C` dispatch.

Everything here is UNTRUSTED meta code: it produces proof terms the
kernel re-checks against the trusted layer (`Assemble`/`Check`).
Failure is a tactic failure — sound rejection, never unsound acceptance.

The deliverables: `toRefutationGoal` (Slice 2) reduces the main goal
`Γ ⊢ G` to the walk's refutation goal
`∀ ρ, (integrality hyps) → (∀ C ∈ Cs, clauseHolds ρ atoms C) → False`;
`orchestrate` (Slice 3, the `nla_solve` dev tactic) runs the full
pipeline — reify → register → `Solver.checkCapturing` (the permutation
seam; decision A) → proxy-def patch → referenced-inputs Cs rebuild →
bridges against the PATCHED internal-order table →
`Walk.walkRefutation` — closing the goal end-to-end, with the SAT-exit
model display (decision 4) and the undef bounded-exit error;
`nonlinearArithCore` + the `nonlinear_arith`/`nonlinear_arith_stats`
elabs (Slice 4) layer it behind the sandboxed L1 `saturateCore` fast
path with per-layer fresh heartbeat budgets (DESIGN-endgame §2.7).
-/

namespace LeanNonlinearArith.Nlsat.Frontend

open Lean Meta Elab Tactic
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check
open LeanNonlinearArith.Nlsat.Quote

/-! ## Quoting

The atom/BoolDef quoters moved to `Nlsat/Quote.lean` at Slice 3
(`atomToExpr`/`atomsToExpr`/…, shared with the snapshot quoters);
`rhoStarExpr` stays here (the frontend's `ρ` instantiation). -/

/-- The `ρ` instantiation: `fun i => if i = 0 then v₀ else … else 0`
with `vᵢ` the slot's ℝ-level value expr. (Reduction check: the kernel
beta/iota-reduces the application at a literal index through the
`Nat.decEq` chain — the same machinery the `#[…][i]?` pins rely on.) -/
def rhoStarExpr (vals : Array Expr) : MetaM Expr := do
  withLocalDecl `i .default (mkConst ``Nat) fun iE => do
    let base ← mkNumeral (mkConst ``Real) 0
    let rec goL : List Expr → Nat → MetaM Expr
      | [], _ => pure base
      | v :: rest, k => do
        let cond ← mkAppM ``Eq #[iE, toExpr k]
        let inner ← goL rest (k + 1)
        mkAppM ``ite #[cond, v, inner]
    mkLambdaFVars #[iE] (← goL vals.toList 0)

/-! ## Reify state -/

/-- Which number type a source expression lives at. -/
inductive ArithTy | int | nat | real deriving BEq, Repr, Inhabited

/-- The elimination plan for a root clause: how to go from the source
hypothesis's proof to a `BoolDef.eval` witness for the clause's form. -/
inductive ElimTree where
  | witness (l : Literal) (userE : Expr)   -- a disjunct holding
  | elimFalse (userE : Expr)               -- a `.fls` disjunct (empty clause)
  | orE (t1 t2 : ElimTree)                 -- h : _ ∨ _ — Or.elim
  | andL (t : ElimTree)                    -- h : _ ∧ _ — And.left then t
  | andR (t : ElimTree)                    -- And.right then t

/-- The six comparison forms over the difference poly. -/
inductive CmpKind | lt | le | gt | ge | eq | ne deriving BEq

/-- A comparison, decoded for the bridge chains. -/
structure CmpInfo where
  a : Expr          -- source-level operands
  b : Expr
  ty : ArithTy
  ck : CmpKind
  /-- the user-side proposition (polarity-folded: the reified literal
  bridges THIS, e.g. `¬(a < b)` for a negated literal) -/
  userSide : Expr

/-- A root clause: the source proof + the hyp's original and expanded
propositions (for the NNF bridge) + the elimination plan. -/
structure RootEntry where
  clause : List Literal
  hypE : Expr
  origE : Expr
  expandedE : Expr
  plan : ElimTree

structure ReifyState where
  /-- ℝ-level value expr per slot (for `ρ*`). -/
  vars : Array Expr := #[]
  /-- source-level key expr per slot (dedup). -/
  varKeys : Array Expr := #[]
  varTy : Array ArithTy := #[]
  /-- the atom table; slot 0 is z3's true-bvar reservation (`none`). -/
  atoms : Array (Option Atom) := #[none]
  /-- arith atom dedup: (kind, difference poly) ↦ bvar. -/
  arithMap : Std.HashMap (IneqKind × MPoly) Nat := {}
  /-- per arith literal: its comparison info. -/
  litProps : Std.HashMap Literal CmpInfo := {}
  /-- per proxy bvar: (def, user-side prop). -/
  proxies : Std.HashMap Nat (BoolDef × Expr) := {}
  /-- definitional clauses: (clause, defined proxy). -/
  defClauses : Array (List Literal × Nat) := #[]
  /-- root clauses. -/
  roots : Array RootEntry := #[]
  /-- hyps skipped as inert (outside the arithmetic fragment — ∀/∃/
  unsupported-type comparisons/prop applications; z3's spinoff-inert
  class: present in the query, never consumed by nlsat). Reported in
  the SAT-exit message. -/
  skippedInert : Nat := 0

abbrev RM := StateT ReifyState TacticM

/-- The arith type of a source expr, if ℤ/ℕ/ℝ. -/
def arithTyOf (tyE : Expr) : Option ArithTy :=
  if tyE.isConstOf ``Int then some .int
  else if tyE.isConstOf ``Nat then some .nat
  else if tyE.isConstOf ``Real then some .real
  else none

/-- The ℝ-level value expr for a source expr of the given type (target
pinned — `Int.cast`'s `R` is otherwise an unsynthesizable mvar). -/
def toRealExpr (e : Expr) (ty : ArithTy) : MetaM Expr :=
  match ty with
  | .int => mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some e]
  | .nat => mkAppOptM ``Nat.cast #[some (mkConst ``Real), none, some e]
  | .real => pure e

/-- Find-or-add a variable slot for source expr `srcE`. -/
def varOf (srcE : Expr) (ty : ArithTy) : RM Nat := do
  let s ← get
  if let some i := s.varKeys.findIdx? (· == srcE) then return i
  let valE ← toRealExpr srcE ty
  modify fun s => { s with
    vars := s.vars.push valE, varKeys := s.varKeys.push srcE,
    varTy := s.varTy.push ty }
  return s.vars.size

/-- Reify an arithmetic term to an `MPoly` over the var table.
div/mod hard-fail (L1-owned invariant, §2.7); other non-polynomial
subterms become fresh variables (z3's uninterpreted-content treatment —
design review R-iii: matches z3's opacity on e.g. if-else ghosts). -/
partial def reifyArith (e : Expr) : RM MPoly := do
  let e := e.consumeMData
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    return MPoly.add (← reifyArith a) (← reifyArith b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) =>
    return MPoly.sub (← reifyArith a) (← reifyArith b)
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    return MPoly.mul (← reifyArith a) (← reifyArith b)
  | (``Neg.neg, #[_, _, a]) =>
    return MPoly.neg (← reifyArith a)
  | (``HPow.hPow, #[_, _, _, _, a, k]) =>
    match k.rawNatLit? with
    | some n =>
      let pa ← reifyArith a
      let rec go : Nat → MPoly → MPoly
        | 0, acc => acc
        | n + 1, acc => go n (MPoly.mul pa acc)
      return go n (MPoly.ofInt 1)
    | none => throwError "nonlinear_arith: non-literal exponent {e}"
  | (``OfNat.ofNat, #[_, n, _]) =>
    match n.rawNatLit? with
    | some v => return MPoly.ofInt v
    | none => throwError "nonlinear_arith: non-literal OfNat {e}"
  | (``Int.cast, #[_, _, a]) => reifyArith a
  | (``Nat.cast, #[_, _, a]) => reifyArith a
  | (``Int.ofNat, #[a]) => reifyArith a
  | (``HDiv.hDiv, _) =>
    throwError "nonlinear_arith: div reaches the L2 frontend — the L1-owned invariant is broken: {e}"
  | (``HMod.hMod, _) =>
    throwError "nonlinear_arith: mod reaches the L2 frontend — the L1-owned invariant is broken: {e}"
  | _ =>
    let tyE ← inferType e
    match arithTyOf tyE with
    | some ty => return MPoly.ofVar (← varOf e ty)
    | none => throwError "nonlinear_arith: non-arithmetic subterm {e}"

/-! ## Comparisons -/

/-- Reify a comparison `a ⋈ b` (or its negation, polarity-folded) to a
solver literal: one atom per (kind, difference-poly) — lt/ge and gt/le
and eq/ne SHARE the atom with flipped polarity (z3's atom-table dedup
spirit). Registers the literal's bridge info. -/
def reifyCmp (ck : CmpKind) (a b origE : Expr) (ty : ArithTy) (pol : Bool) : RM Literal := do
  let pa ← reifyArith a
  let pb ← reifyArith b
  let diff := MPoly.sub pa pb
  let (ak, baseNeg) : IneqKind × Bool := match ck with
    | .lt => (.lt, false)   -- a−b < 0
    | .gt => (.gt, false)   -- a−b > 0
    | .eq => (.eq, false)   -- a−b = 0
    | .le => (.gt, true)    -- ¬(a−b > 0)
    | .ge => (.lt, true)    -- ¬(a−b < 0)
    | .ne => (.eq, true)    -- ¬(a−b = 0)
  let s ← get
  let bvar ← match s.arithMap[(ak, diff)]? with
    | some b => pure b
    | none =>
      let b := s.atoms.size
      modify fun s => { s with
        atoms := s.atoms.push (some (.ineq ⟨ak, [(diff, false)]⟩)),
        arithMap := s.arithMap.insert (ak, diff) b }
      pure b
  let lit : Literal := ⟨bvar, baseNeg != !pol⟩
  let userSide ← if pol then pure origE else mkAppM ``Not #[origE]
  modify fun s => { s with
    litProps := s.litProps.insert lit ⟨a, b, ty, ck, userSide⟩ }
  return lit

/-! ## NNF reification of propositions -/

/-- `ite` in proposition position expands to CNF shape. -/
private theorem ite_cnf (c a b : Prop) [Decidable c] :
    ite c a b ↔ (¬c ∨ a) ∧ (c ∨ b) := by
  by_cases hc : c <;> simp [hc]

private theorem not_ite_cnf (c a b : Prop) [Decidable c] :
    ¬ ite c a b ↔ (c ∧ ¬a) ∨ (¬c ∧ ¬b) := by
  by_cases hc : c <;> simp [hc]

/-- (a ↔ b) in CNF shape. -/
private theorem iff_cnf (a b : Prop) : (a ↔ b) ↔ (¬a ∨ b) ∧ (¬b ∨ a) := by
  tauto

/-- ¬(a ↔ b) in DNF-ish shape. -/
private theorem not_iff_cnf (a b : Prop) : ¬(a ↔ b) ↔ (a ∧ ¬b) ∨ (¬a ∧ b) := by
  tauto

/-- Prop equality is iff (the Prop-Eq case of the NNF). -/
private theorem prop_eq_iff (a b : Prop) : (a = b) ↔ (a ↔ b) := by
  exact eq_iff_iff

/-! ## NNF reification -/

/-- A reified proposition: the `BoolDef` form + the user-side prop it
bridges (polarity-folded). -/
abbrev FormE := BoolDef × Expr

/-- NNF reification: a proposition to a `BoolDef` over solver literals
plus the EXPANDED proposition mirroring the form structurally (the
bridge `orig ↔ expanded` is built separately by `mkNnfIff`; the
elimination plans navigate the expanded tree). Negations push through
the Boolean grammar; comparison negations fold into the literal's
polarity. Unsupported shapes fail loudly HERE; the phase-1 driver
decides per hyp whether a failure throws (the goal, div/mod) or skips
the hyp as inert (nla-15 — z3's spinoff-inert class). -/
partial def reifyProp (e : Expr) (pol : Bool) : RM FormE := do
  let e := e.consumeMData
  match e with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then
      throwError "nonlinear_arith: dependent ∀ unsupported: {e}"
    else
      -- implication
      if pol then
        let (fa, ea) ← reifyProp a false
        let (fb, eb) ← reifyProp b true
        return (.or fa fb, ← mkAppM ``Or #[ea, eb])
      else
        let (fa, ea) ← reifyProp a true
        let (fb, eb) ← reifyProp b false
        return (.and fa fb, ← mkAppM ``And #[ea, eb])
  | _ =>
  match e.getAppFnArgs with
  | (``Not, #[p]) => reifyProp p (!pol)
  | (``And, #[a, b]) =>
    if pol then
      let (fa, ea) ← reifyProp a true
      let (fb, eb) ← reifyProp b true
      return (.and fa fb, ← mkAppM ``And #[ea, eb])
    else
      let (fa, ea) ← reifyProp a false
      let (fb, eb) ← reifyProp b false
      return (.or fa fb, ← mkAppM ``Or #[ea, eb])
  | (``Or, #[a, b]) =>
    if pol then
      let (fa, ea) ← reifyProp a true
      let (fb, eb) ← reifyProp b true
      return (.or fa fb, ← mkAppM ``Or #[ea, eb])
    else
      let (fa, ea) ← reifyProp a false
      let (fb, eb) ← reifyProp b false
      return (.and fa fb, ← mkAppM ``And #[ea, eb])
  | (``Iff, #[a, b]) =>
    let (faT, eaT) ← reifyProp a true
    let (faF, eaF) ← reifyProp a false
    let (fbT, ebT) ← reifyProp b true
    let (fbF, ebF) ← reifyProp b false
    if pol then
      return (.and (.or faF fbT) (.or fbF faT),
        ← mkAppM ``And #[← mkAppM ``Or #[eaF, ebT], ← mkAppM ``Or #[ebF, eaT]])
    else
      return (.or (.and faT fbF) (.and faF fbT),
        ← mkAppM ``Or #[← mkAppM ``And #[eaT, ebF], ← mkAppM ``And #[eaF, ebT]])
  | (``ite, #[ty, c, _, a, b]) =>
    if !(← isDefEq ty (mkSort levelZero)) then
      throwError "nonlinear_arith: ite at non-Prop type {e}"
    let (fcT, ecT) ← reifyProp c true
    let (fcF, ecF) ← reifyProp c false
    let (faT, eaT) ← reifyProp a true
    let (faF, eaF) ← reifyProp a false
    let (fbT, ebT) ← reifyProp b true
    let (fbF, ebF) ← reifyProp b false
    if pol then
      return (.and (.or fcF faT) (.or fcT fbT),
        ← mkAppM ``And #[← mkAppM ``Or #[ecF, eaT], ← mkAppM ``Or #[ecT, ebT]])
    else
      return (.or (.and fcT faF) (.and fcF fbF),
        ← mkAppM ``Or #[← mkAppM ``And #[ecT, eaF], ← mkAppM ``And #[ecF, ebF]])
  | _ =>
    if e.isConstOf ``True then
      return ((if pol then .tru else .fls), if pol then e else mkConst ``False)
    if e.isConstOf ``False then
      return ((if pol then .fls else .tru), if pol then e else mkConst ``True)
    -- comparisons
    match e.getAppFnArgs with
    | (``Eq, #[ty, a, b]) =>
      match arithTyOf ty with
      | some aty =>
        let userSide ← if pol then pure e else mkAppM ``Not #[e]
        return (.lit (← reifyCmp .eq a b e aty pol), userSide)
      | none =>
        if (← isDefEq ty (mkSort levelZero)) then
          -- Prop equality: expand as Iff (propext bridge in mkNnfIff)
          let (faT, eaT) ← reifyProp a true
          let (faF, eaF) ← reifyProp a false
          let (fbT, ebT) ← reifyProp b true
          let (fbF, ebF) ← reifyProp b false
          if pol then
            return (.and (.or faF fbT) (.or fbF faT),
              ← mkAppM ``And #[← mkAppM ``Or #[eaF, ebT], ← mkAppM ``Or #[ebF, eaT]])
          else
            return (.or (.and faT fbF) (.and faF fbT),
              ← mkAppM ``Or #[← mkAppM ``And #[eaT, ebF], ← mkAppM ``And #[eaF, ebT]])
        throwError "nonlinear_arith: equality at unsupported type {ty}: {e}"
    | (``Ne, #[ty, a, b]) =>
      match arithTyOf ty with
      | some aty =>
        let userSide ← if pol then pure e else mkAppM ``Not #[e]
        return (.lit (← reifyCmp .ne a b e aty pol), userSide)
      | none => throwError "nonlinear_arith: Ne at unsupported type: {e}"
    | (``LT.lt, #[ty, _, a, b]) =>
      match arithTyOf ty with
      | some aty =>
        let userSide ← if pol then pure e else mkAppM ``Not #[e]
        return (.lit (← reifyCmp .lt a b e aty pol), userSide)
      | none => throwError "nonlinear_arith: < at unsupported type: {e}"
    | (``LE.le, #[ty, _, a, b]) =>
      match arithTyOf ty with
      | some aty =>
        let userSide ← if pol then pure e else mkAppM ``Not #[e]
        return (.lit (← reifyCmp .le a b e aty pol), userSide)
      | none => throwError "nonlinear_arith: ≤ at unsupported type: {e}"
    | (``GT.gt, #[ty, _, a, b]) =>
      match arithTyOf ty with
      | some aty =>
        let userSide ← if pol then pure e else mkAppM ``Not #[e]
        return (.lit (← reifyCmp .gt a b e aty pol), userSide)
      | none => throwError "nonlinear_arith: > at unsupported type: {e}"
    | (``GE.ge, #[ty, _, a, b]) =>
      match arithTyOf ty with
      | some aty =>
        let userSide ← if pol then pure e else mkAppM ``Not #[e]
        return (.lit (← reifyCmp .ge a b e aty pol), userSide)
      | none => throwError "nonlinear_arith: ≥ at unsupported type: {e}"
    | _ => throwError "nonlinear_arith: unsupported hypothesis shape: {e}"

/-! ## Tseitin clausification -/

/-- A literal as a NORMALIZED form: positive-polarity leaf, negation
as a node (the proxy-def invariant — `normNeg`-stable). -/
def normLitForm (l : Literal) : BoolDef :=
  if l.neg then .neg (.lit ⟨l.bvar, false⟩) else .lit l

/-- Fresh proxy for a connective form whose children are already
literals: registers the def (NORMALIZED at the leaves) + definitional
clauses (the taut forms are recomputed at bridge time via
`inlineProxy`; children stay abstract so checks are local — design
review R-i). Returns the positive literal. -/
def mkProxy (defPre : BoolDef) (ud : Expr) : RM Literal := do
  let p := (← get).atoms.size
  match defPre with
  | .and (.lit la) (.lit lb) =>
    let defCore := BoolDef.and (normLitForm la) (normLitForm lb)
    modify fun s => { s with
      atoms := s.atoms.push (some (.bool defCore)),
      proxies := s.proxies.insert p (defCore, ud),
      defClauses := s.defClauses
        |>.push ([⟨p, true⟩, la], p)
        |>.push ([⟨p, true⟩, lb], p)
        |>.push ([⟨p, false⟩, la.negate, lb.negate], p) }
    return ⟨p, false⟩
  | .or (.lit la) (.lit lb) =>
    let defCore := BoolDef.or (normLitForm la) (normLitForm lb)
    modify fun s => { s with
      atoms := s.atoms.push (some (.bool defCore)),
      proxies := s.proxies.insert p (defCore, ud),
      defClauses := s.defClauses
        |>.push ([⟨p, true⟩, la, lb], p)
        |>.push ([⟨p, false⟩, la.negate], p)
        |>.push ([⟨p, false⟩, lb.negate], p) }
    return ⟨p, false⟩
  | _ => throwError "nonlinear_arith: internal: proxy def not a binary connective"

/-- Tseitin-lift a form to a single literal, proxying connectives
(children first — emission order = the `boolDefsOrdered` invariant). -/
partial def tseitinLit (fe : FormE) : RM Literal := do
  match fe with
  | (.lit l, _) => return l
  | (.and fa fb, ud) =>
    let (ua, ub) ← match ud.getAppFnArgs with
      | (``And, #[ua, ub]) => pure (ua, ub)
      | _ => throwError "nonlinear_arith: internal: and-form with non-And user prop {ud}"
    let la ← tseitinLit (fa, ua)
    let lb ← tseitinLit (fb, ub)
    mkProxy (.and (.lit la) (.lit lb)) ud
  | (.or fa fb, ud) =>
    let (ua, ub) ← match ud.getAppFnArgs with
      | (``Or, #[ua, ub]) => pure (ua, ub)
      | _ => throwError "nonlinear_arith: internal: or-form with non-Or user prop {ud}"
    let la ← tseitinLit (fa, ua)
    let lb ← tseitinLit (fb, ub)
    mkProxy (.or (.lit la) (.lit lb)) ud
  | (f, ud) =>
    throwError "nonlinear_arith: internal: tseitinLit on {repr f} / {ud}"

/-- Does the form contain a `tru` leaf (making an enclosing or-clause
tautological)? -/
def formHasTru : BoolDef → Bool
  | .tru => true
  | .and a b | .or a b => formHasTru a || formHasTru b
  | .neg a => formHasTru a
  | _ => false

/-- Collect an or-node's clause: literal list + elim plan mirroring the
EXPANDED prop's Or-nesting (binary, as built by reifyProp). Non-leaf
disjuncts are Tseitin-proxied; fls disjuncts stay in the plan (their
branch dies by False.elim); a tru anywhere voids the clause. -/
partial def orCollect (fe : FormE) : RM (List Literal × ElimTree) := do
  match fe with
  | (.or fa fb, ud) =>
    match ud.getAppFnArgs with
    | (``Or, #[ua, ub]) =>
      let (litsL, planL) ← orCollect (fa, ua)
      let (litsR, planR) ← orCollect (fb, ub)
      return (litsL ++ litsR, .orE planL planR)
    | _ => throwError "nonlinear_arith: internal: or-form with non-Or prop {ud}"
  | (.lit l, ud) => return ([l], .witness l ud)
  | (.fls, ud) => return ([], .elimFalse ud)
  | (.and _ _, ud) =>
    let l ← tseitinLit fe
    return ([l], .witness l ud)
  | (f, ud) =>
    throwError "nonlinear_arith: internal: orCollect on {repr f} / {ud}"

/-- Clausify a reified hyp form into root clauses appended to the
state. `wrap` navigates from the hyp's full expanded form to this node
(andL/andR). Tautological clauses (tru in the disjunction) are dropped
— sound weakening. -/
partial def clausify (hypE origE expandedE : Expr) (fe : FormE)
    (wrap : ElimTree → ElimTree) : RM Unit := do
  match fe with
  | (.and fa fb, ud) =>
    match ud.getAppFnArgs with
    | (``And, #[ua, ub]) =>
      clausify hypE origE expandedE (fa, ua) (fun t => wrap (.andL t))
      clausify hypE origE expandedE (fb, ub) (fun t => wrap (.andR t))
    | _ => throwError "nonlinear_arith: internal: and-form with non-And prop {ud}"
  | (.or _ _, ud) =>
    unless formHasTru fe.1 do
      let (lits, plan) ← orCollect fe
      modify fun s => { s with roots := s.roots.push (⟨lits, hypE, origE, expandedE, wrap plan⟩) }
  | (.lit l, ud) =>
    modify fun s => { s with roots := s.roots.push (⟨[l], hypE, origE, expandedE, wrap (.witness l ud)⟩) }
  | (.tru, _) => pure ()
  | (.fls, ud) =>
    modify fun s => { s with roots := s.roots.push (⟨[], hypE, origE, expandedE, wrap (.elimFalse ud)⟩) }
  | (.neg _, ud) => throwError "nonlinear_arith: internal: neg node past NNF: {ud}"


/-! ## Phase 2: bridge construction (term-mode; the only sandbox is the
per-literal evalP-alignment — the Refute-sandbox idiom) -/

/-- Bridge-construction context: the final table/ρ* Exprs, the
decide-discharged emission-order invariant, and the registries. -/
structure BridgeCtx where
  ρStar : Expr
  atomsE : Expr
  atoms : Array (Option Atom)
  /-- proof of `boolDefsOrdered atomsE = true` -/
  hordPrf : Expr
  /-- `litHolds ρ* atomsE` as a curried application (the eval oracle) -/
  oracleE : Expr
  litProps : Std.HashMap Literal CmpInfo
  proxies : Std.HashMap Nat (BoolDef × Expr)
  litCache : IO.Ref (Std.HashMap Literal Expr)
  proxyCache : IO.Ref (Std.HashMap Nat Expr)

def mkIffTrans (a b : Expr) : MetaM Expr := mkAppM ``Iff.trans #[a, b]
def mkIffSymm (a : Expr) : MetaM Expr := mkAppM ``Iff.symm #[a]
def mkNotCongr (a : Expr) : MetaM Expr := mkAppM ``not_congr #[a]
/-- `BoolDef.eval oracleE form` as an Expr application. -/
def evalAppE (bctx : BridgeCtx) (form : BoolDef) : Expr :=
  mkApp2 (mkConst ``BoolDef.eval) bctx.oracleE (boolDefToExpr form)


/-- The alignment equation `evalP ρ* p = diff` — sandboxed
(withoutModifyingState + runtime-ex catch + mvar check; the
probe-pinned script `simp [evalP, evalM]; push_cast; ring`). The proof
term is extracted INSIDE the sandbox (assignments roll back, the term
survives). -/
def mkAlign (bctx : BridgeCtx) (p : MPoly) (diffE : Expr) : TacticM Expr := do
  let pE := toExpr p
  let evalE ← mkAppM ``Check.evalP #[bctx.ρStar, pE]
  let goalTy ← mkAppM ``Eq #[evalE, diffE]
  let m ← mkFreshExprMVar goalTy
  let r ← withoutModifyingState do
    let saved ← getGoals
    setGoals [m.mvarId!]
    let r ← tryCatchRuntimeEx
      (do
        -- `try` each step: simp can fully close linear alignments
        -- (Slice-3, o139: `evalP ρ* [(-1,[(1,1)])] = 0 - da` closes by
        -- reduction), and a trailing step on zero goals must not fail
        -- the sandbox.
        evalTactic (← `(tactic| simp [Check.evalP, Check.evalM]))
        evalTactic (← `(tactic| try push_cast))
        evalTactic (← `(tactic| try ring))
        let pf ← instantiateMVars m
        if pf.hasMVar then return none
        return some pf)
      (fun _ => return none)
    setGoals saved
    return r
  match r with
  | some pf => return pf
  | none =>
    throwError "nonlinear_arith: alignment discharge failed:\n{goalTy}"

/-- The per-literal chain: `info.userSide ↔ litHolds ρ* atomsE ℓ`.
Term-mode Iff.trans chains over: `holds_single_*` (atom semantics), the
align-Eq (`Iff.of_eq ∘ congrArg`), the `sub_*` zero-shifts, and the
cast links (`Int.cast_*`/`Nat.cast_*`). The `litHolds` side closes by
defeq ascription (concrete table lookups are kernel-reducible). -/
def mkLitIff (bctx : BridgeCtx) (lit : Literal) : TacticM Expr := do
  let cache ← bctx.litCache.get
  if let some pf := cache[lit]? then return pf
  let some info := bctx.litProps[lit]?
    | throwError "nonlinear_arith: internal: unregistered literal {repr lit}"
  let some (some (.ineq ia)) := bctx.atoms[lit.bvar]?
    | throwError "nonlinear_arith: internal: literal {repr lit} not an ineq atom"
  let p := ia.factors.head!.1
  let castA ← toRealExpr info.a info.ty
  let castB ← toRealExpr info.b info.ty
  let diffE ← mkAppM ``HSub.hSub #[castA, castB]
  let alignE ← mkAlign bctx p diffE
  let pE := toExpr p
  -- the congrArg motive for the sign condition
  let signLam (shape : Name) (swap : Bool) : MetaM Expr :=
    withLocalDecl `x .default (mkConst ``Real) fun xE => do
      let z ← mkNumeral (mkConst ``Real) 0
      let body ← if swap then mkAppM shape #[z, xE] else mkAppM shape #[xE, z]
      mkLambdaFVars #[xE] body
  let mkC3 (shape : Name) (swap : Bool) : TacticM Expr := do
    let lam ← signLam shape swap
    let cong ← mkAppM ``congrArg #[lam, alignE]
    mkAppM ``Iff.of_eq #[cong]
  let holdsSingle (lem : Name) : MetaM Expr := do
    mkAppM lem #[bctx.ρStar, pE]
  -- cast links: the leaf lemmas' operands are IMPLICIT — mkAppOptM with
  -- pinned positions (house idiom; binder counts from #print):
  -- Int.cast_{lt,le} 8 binders, Nat.cast_{lt,le} 8, *_cast_inj 5,
  -- sub_lt_zero/sub_pos 6, sub_eq_zero 4, not_lt 4.
  let castLinkLt (x y : Expr) : MetaM Expr :=
    match info.ty with
    | .int => mkAppOptM ``Int.cast_lt #[some (mkConst ``Real), none, none, none, none, none, some x, some y]
    | .nat => mkAppOptM ``Nat.cast_lt #[some (mkConst ``Real), none, none, none, none, none, some x, some y]
    | .real => do mkAppM ``Iff.refl #[← mkAppM ``LT.lt #[x, y]]
  let castLinkLe (x y : Expr) : MetaM Expr :=
    match info.ty with
    | .int => mkAppOptM ``Int.cast_le #[some (mkConst ``Real), none, none, none, none, none, some x, some y]
    | .nat => mkAppOptM ``Nat.cast_le #[some (mkConst ``Real), none, none, none, none, none, some x, some y]
    | .real => do mkAppM ``Iff.refl #[← mkAppM ``LE.le #[x, y]]
  let castLinkEq (x y : Expr) : MetaM Expr :=
    match info.ty with
    | .int => mkAppOptM ``Int.cast_inj #[some (mkConst ``Real), none, none, some x, some y]
    | .nat => mkAppOptM ``Nat.cast_inj #[some (mkConst ``Real), none, none, some x, some y]
    | .real => do mkAppM ``Iff.refl #[← mkAppM ``Eq #[x, y]]
  let subLtZero (x y : Expr) : MetaM Expr :=
    mkAppOptM ``sub_lt_zero #[none, none, none, none, some x, some y]
  let subPos (x y : Expr) : MetaM Expr :=
    mkAppOptM ``sub_pos #[none, none, none, none, some x, some y]
  let subEqZero (x y : Expr) : MetaM Expr :=
    mkAppOptM ``sub_eq_zero #[none, none, some x, some y]
  let notLt (x y : Expr) : MetaM Expr :=
    mkAppOptM ``not_lt #[none, none, some x, some y]
  -- pieces of the positive chain: c1 = cast link, c2 = sub-shift,
  -- c3 = align, c4 = holds_single
  let (c1, c2, c3, c4) ← match ia.kind with
    | .lt =>
      pure (← castLinkLt info.a info.b, ← subLtZero castA castB,
        ← mkC3 ``LT.lt false, ← holdsSingle ``holds_single_lt)
    | .gt =>
      pure (← castLinkLt info.b info.a, ← subPos castA castB,
        ← mkC3 ``LT.lt true, ← holdsSingle ``holds_single_gt)
    | .eq =>
      pure (← castLinkEq info.a info.b, ← subEqZero castA castB,
        ← mkC3 ``Eq false, ← holdsSingle ``holds_single_eq)
  -- posChain: userPlus ↔ litHolds ⟨b,false⟩ (assembled from the user side)
  let posChain ← mkIffTrans (← mkIffSymm c1) (← mkIffTrans (← mkIffSymm c2)
    (← mkIffTrans (← mkIffSymm c3) (← mkIffSymm c4)))
  -- tailChain: (cast-level positive) ↔ litHolds ⟨b,false⟩
  let tailChain ← mkIffTrans (← mkIffSymm c2)
    (← mkIffTrans (← mkIffSymm c3) (← mkIffSymm c4))
  let full : Expr ← match info.ck, lit.neg with
    | .lt, true | .eq, true | .gt, true => mkNotCongr posChain
    | .ne, true => mkNotCongr posChain
    | .ne, false =>
      let eqE ← mkAppM ``Eq #[info.a, info.b]
      mkIffTrans (← mkAppOptM ``not_not #[some eqE]) posChain
    | .lt, false | .eq, false | .gt, false => pure posChain
    | .le, true =>
      let t1 ← mkIffSymm (← castLinkLe info.a info.b)
      let t2 ← mkIffSymm (← notLt castB castA)
      mkIffTrans t1 (← mkIffTrans t2 (← mkNotCongr tailChain))
    | .ge, true =>
      let t1 ← mkIffSymm (← castLinkLe info.b info.a)
      let t2 ← mkIffSymm (← notLt castA castB)
      mkIffTrans t1 (← mkIffTrans t2 (← mkNotCongr tailChain))
    | .le, false =>
      -- ¬(a ≤ b) ↔ litHolds ⟨b,false⟩ (positive gt atom): not_congr on
      -- the cast link, then not_le, then the tail. (Kernel-caught at
      -- o139: the pre-Slice-3 arm double-negated to ¬¬litHolds.)
      let t1 ← mkNotCongr (← mkIffSymm (← castLinkLe info.a info.b))
      let t2 ← mkAppOptM ``not_le
        #[some (mkConst ``Real), none, some castA, some castB]
      mkIffTrans t1 (← mkIffTrans t2 tailChain)
    | .ge, false =>
      -- ¬(a ≥ b) = ¬(b ≤ a) ↔ litHolds ⟨b,false⟩ (positive lt atom).
      let t1 ← mkNotCongr (← mkIffSymm (← castLinkLe info.b info.a))
      let t2 ← mkAppOptM ``not_le
        #[some (mkConst ``Real), none, some castB, some castA]
      mkIffTrans t1 (← mkIffTrans t2 tailChain)
  -- (the CmpKind.ne case shares .eq's atom with baseNeg — covered by the
  -- (_, false)/(_, true) split via posChain/not_congr)
  let litE := Refute.litToExpr lit
  let targetRhs ← mkAppM ``litHolds #[bctx.ρStar, bctx.atomsE, litE]
  let targetTy ← mkAppM ``Iff #[info.userSide, targetRhs]
  let result ← mkExpectedTypeHint full targetTy
  bctx.litCache.modify (·.insert lit result)
  return result

/-- Decodability witness for a table slot: `∃ a, atomsE[b]? = some (some a)`
— the table lookup by decide, the intro by construction. -/
def mkDecodableProof (bctx : BridgeCtx) (b : Nat) : MetaM Expr := do
  let some (some a) := bctx.atoms[b]?
    | throwError "nonlinear_arith: internal: junk slot at {b}"
  let aE := atomToExpr a
  let lookupTy ← do
    let lhs ← mkAppM ``getElem? #[bctx.atomsE, toExpr b]
    let inner := mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``Atom) aE
    let outer := mkApp2 (mkConst ``Option.some [levelZero])
      (mkApp (mkConst ``Option [levelZero]) (mkConst ``Atom)) inner
    mkAppM ``Eq #[lhs, outer]
  let decPrf ← mkDecideProof lookupTy
  let predLam ← withLocalDecl `a .default (mkConst ``Atom) fun aE => do
    let eqTy ← mkAppM ``Eq #[← mkAppM ``getElem? #[bctx.atomsE, toExpr b],
      mkApp2 (mkConst ``Option.some [levelZero])
        (mkApp (mkConst ``Option [levelZero]) (mkConst ``Atom))
        (mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``Atom) aE)]
    mkLambdaFVars #[aE] eqTy
  mkAppOptM ``Exists.intro #[none, some predLam, some aE, some decPrf]

mutual
/-- `expandedE ↔ BoolDef.eval oracleE formE` — recursion mirroring the
form (eval's arms are structural, so the congruences are defeq
ascriptions); proxy leaves use the registered proxy Iffs. -/
partial def mkFormIff (bctx : BridgeCtx) (form : BoolDef) (expandedE : Expr) :
    TacticM Expr := do
  let ascribe (pf : Expr) : MetaM Expr := do
    let formE := boolDefToExpr form
    let evalE := mkApp2 (mkConst ``BoolDef.eval) bctx.oracleE formE
    let targetTy ← mkAppM ``Iff #[expandedE, evalE]
    mkExpectedTypeHint pf targetTy
  match form with
  | .lit l =>
    match bctx.atoms[l.bvar]! with
    | some (.bool _) =>
      let base ← mkProxyIff bctx l.bvar
      let pf ← if l.neg then mkNotCongr base else pure base
      ascribe pf
    | some (.ineq _) => ascribe (← mkLitIff bctx l)
    | _ => throwError "nonlinear_arith: internal: leaf at junk slot {repr l}"
  | .and a b =>
    let (ua, ub) ← match expandedE.getAppFnArgs with
      | (``And, #[ua, ub]) => pure (ua, ub)
      | _ => throwError "nonlinear_arith: internal: and-form, non-And expanded {expandedE}"
    ascribe (← mkAppM ``and_congr #[← mkFormIff bctx a ua, ← mkFormIff bctx b ub])
  | .or a b =>
    let (ua, ub) ← match expandedE.getAppFnArgs with
      | (``Or, #[ua, ub]) => pure (ua, ub)
      | _ => throwError "nonlinear_arith: internal: or-form, non-Or expanded {expandedE}"
    ascribe (← mkAppM ``or_congr #[← mkFormIff bctx a ua, ← mkFormIff bctx b ub])
  | .neg a =>
    match expandedE.getAppFnArgs with
    | (``Not, #[ua]) => ascribe (← mkNotCongr (← mkFormIff bctx a ua))
    | _ =>
      -- the normed-proxy-def leaf: `.neg (.lit ⟨b,false⟩)` paired with
      -- the child's non-Not user prop (e.g. `x ≥ 1`) — the chain is
      -- litIff(⟨b,true⟩) ∘ litHolds_negate.
      match a with
      | .lit l =>
        if l.neg then
          throwError "nonlinear_arith: internal: normed def has a negative leaf"
        else
          let lPos : Literal := ⟨l.bvar, false⟩
          let base ← mkLitIff bctx ⟨l.bvar, true⟩
          let hdec ← mkDecodableProof bctx l.bvar
          let neg ← mkAppM ``litHolds_negate #[bctx.ρStar, bctx.atomsE,
            Refute.litToExpr lPos, hdec]
          ascribe (← mkIffTrans base neg)
      | _ => throwError "nonlinear_arith: internal: neg node over non-literal"

  | .tru => ascribe (← mkAppM ``Iff.refl #[expandedE])
  | .fls => ascribe (← mkAppM ``Iff.refl #[expandedE])

/-- The registered proxy Iff: `ud ↔ litHolds ρ* atomsE ⟨p, false⟩` via
`litHolds_bool` (slot lookup by decide) + `boolDefHolds_evalLitHolds`
(order invariant by decide) + `mkFormIff` on the def. -/
partial def mkProxyIff (bctx : BridgeCtx) (p : Nat) : TacticM Expr := do
  let cache ← bctx.proxyCache.get
  if let some pf := cache[p]? then return pf
  let some (defCore, ud) := bctx.proxies[p]?
    | throwError "nonlinear_arith: internal: unregistered proxy {p}"
  let defE := boolDefToExpr defCore
  -- table lookup fact, kernel-decided
  let lookupTy ← do
    let lhs ← mkAppM ``getElem? #[bctx.atomsE, toExpr p]
    let inner := mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``Atom)
      (atomToExpr (.bool defCore))
    let outer := mkApp2 (mkConst ``Option.some [levelZero])
      (mkApp (mkConst ``Option [levelZero]) (mkConst ``Atom)) inner
    mkAppM ``Eq #[lhs, outer]
  let lookupPrf ← mkDecideProof lookupTy
  -- h1 : litHolds ⟨p,false⟩ ↔ bDH size def
  let h1 ← mkAppM ``litHolds_bool
    #[bctx.ρStar, bctx.atomsE, toExpr p, mkConst ``Bool.false, defE, lookupPrf]
  -- h2 : bDH size def ↔ eval oracle def
  let sizeE ← mkAppM ``Array.size #[bctx.atomsE]
  let pltTy ← do
    let app ← mkAppM ``proxyLeavesLT #[bctx.atomsE, sizeE, defE]
    mkAppM ``Eq #[app, mkConst ``Bool.true]
  let pltPrf ← mkDecideProof pltTy
  let h2 ← mkAppM ``boolDefHolds_evalLitHolds
    #[bctx.ρStar, bctx.atomsE, bctx.hordPrf, sizeE, defE, pltPrf]
  -- h3 : ud ↔ eval oracle def
  let h3 ← mkFormIff bctx defCore ud
  -- compose: ud ↔ eval ↔ bDH ↔ litHolds
  let result ← mkIffTrans h3 (← mkIffTrans (← mkIffSymm h2) (← mkIffSymm h1))
  let targetTy ← mkAppM ``Iff #[ud, ← mkAppM ``litHolds
    #[bctx.ρStar, bctx.atomsE, Refute.litToExpr ⟨p, false⟩]]
  let result ← mkExpectedTypeHint result targetTy
  bctx.proxyCache.modify (·.insert p result)
  return result
end

/-- Inline a proxy's def at its own leaves (one level — children stay
abstract). The taut-checkable form of a definitional clause is
`inlineProxy p defCore (normNeg (clauseForm C))`. -/
partial def inlineProxy (p : Nat) (d : BoolDef) : BoolDef → BoolDef
  | .lit l => if l.bvar == p then (if l.neg then .neg d else d) else .lit l
  | .and a b => .and (inlineProxy p d a) (inlineProxy p d b)
  | .or a b => .or (inlineProxy p d a) (inlineProxy p d b)
  | .neg a => .neg (inlineProxy p d a)
  | .tru => .tru
  | .fls => .fls

/-- The shared proxy-boundary facts: `litHolds ⟨p,false⟩ ↔ bDH size def`
(table lookup by decide) and `bDH size def ↔ eval oracle def`
(order invariant + leaf bound by decide). -/
def mkProxyFacts (bctx : BridgeCtx) (p : Nat) : TacticM (Expr × Expr) := do
  let some (defCore, _) := bctx.proxies[p]?
    | throwError "nonlinear_arith: internal: unregistered proxy {p}"
  let defE := boolDefToExpr defCore
  let lookupTy ← do
    let lhs ← mkAppM ``getElem? #[bctx.atomsE, toExpr p]
    let inner := mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``Atom)
      (atomToExpr (.bool defCore))
    let outer := mkApp2 (mkConst ``Option.some [levelZero])
      (mkApp (mkConst ``Option [levelZero]) (mkConst ``Atom)) inner
    mkAppM ``Eq #[lhs, outer]
  let lookupPrf ← mkDecideProof lookupTy
  let h1 ← mkAppM ``litHolds_bool
    #[bctx.ρStar, bctx.atomsE, toExpr p, mkConst ``Bool.false, defE, lookupPrf]
  let sizeE ← mkAppM ``Array.size #[bctx.atomsE]
  let pltTy ← do
    let app ← mkAppM ``proxyLeavesLT #[bctx.atomsE, sizeE, defE]
    mkAppM ``Eq #[app, mkConst ``true]
  let pltPrf ← mkDecideProof pltTy
  let h2 ← mkAppM ``boolDefHolds_evalLitHolds
    #[bctx.ρStar, bctx.atomsE, bctx.hordPrf, sizeE, defE, pltPrf]
  return (h1, h2)

/-- `eval oracle defCore ↔ litHolds ⟨p, false⟩` — the proxy-boundary
link at the eval level. -/
def mkProxyBoundary (bctx : BridgeCtx) (p : Nat) : TacticM Expr := do
  let (h1, h2) ← mkProxyFacts bctx p
  mkIffSymm (← mkIffTrans h1 h2)

/-- The hyp-level NNF bridge: `(pol ? origE : ¬origE) ↔ expandedE` —
term-mode recursion mirroring `reifyProp`, through the named
propositional lemmas (`not_and`, `imp_iff_not_or`, `iff_cnf`, …).
`origE` is mdata-stripped at entry (nla-15: hyp types can carry
elaboration mdata — e.g. hGN's `¬[mdata True]` after a preceding
`have`; without this the True/False literal arms are skipped and the
catch-all builds a refl where `not_true` is needed — kernel-caught).
reifyProp consumes per-recursion; this is its bridge-side twin. -/
partial def mkNnfIff (origE : Expr) (pol : Bool) (expandedE : Expr) : TacticM Expr := do
  let origE := origE.consumeMData
  let userSide ← if pol then pure origE else mkAppM ``Not #[origE]
  let ascribe (pf : Expr) : MetaM Expr := do
    let targetTy ← mkAppM ``Iff #[userSide, expandedE]
    mkExpectedTypeHint pf targetTy
  let decompose (e : Expr) (head : Name) : TacticM (Expr × Expr) :=
    match e.getAppFnArgs with
    | (h, #[x, y]) => if h == head then pure (x, y)
      else throwError "nonlinear_arith: internal: expanded shape mismatch ({head}): {e}"
    | _ => throwError "nonlinear_arith: internal: expanded shape mismatch ({head}): {e}"
  match origE with
  | .forallE _ a b _ =>
    if b.hasLooseBVars then
      throwError "nonlinear_arith: dependent ∀ unsupported: {origE}"
    else if pol then
      let (ex, ey) ← decompose expandedE ``Or
      let step ← mkAppM ``imp_iff_not_or #[a, b]
      ascribe (← mkIffTrans step (← mkAppM ``or_congr
        #[← mkNnfIff a false ex, ← mkNnfIff b true ey]))
    else
      let (ex, ey) ← decompose expandedE ``And
      let step ← mkAppM ``_root_.not_imp #[a, b]
      ascribe (← mkIffTrans step (← mkAppM ``and_congr
        #[← mkNnfIff a true ex, ← mkNnfIff b false ey]))
  | _ =>
  match origE.getAppFnArgs with
  | (``Not, #[q]) =>
    let child ← mkNnfIff q (!pol) expandedE
    if pol then
      ascribe child
    else
      let step ← mkAppOptM ``not_not #[some q]
      ascribe (← mkIffTrans step child)
  | (``And, #[a, b]) =>
    if pol then
      let (ex, ey) ← decompose expandedE ``And
      ascribe (← mkAppM ``and_congr #[← mkNnfIff a true ex, ← mkNnfIff b true ey])
    else
      let (ex, ey) ← decompose expandedE ``Or
      let step ← mkAppM ``not_and #[a, b]
      ascribe (← mkIffTrans step (← mkAppM ``or_congr
        #[← mkNnfIff a false ex, ← mkNnfIff b false ey]))
  | (``Or, #[a, b]) =>
    if pol then
      let (ex, ey) ← decompose expandedE ``Or
      ascribe (← mkAppM ``or_congr #[← mkNnfIff a true ex, ← mkNnfIff b true ey])
    else
      let (ex, ey) ← decompose expandedE ``And
      let step ← mkAppM ``not_or #[a, b]
      ascribe (← mkIffTrans step (← mkAppM ``and_congr
        #[← mkNnfIff a false ex, ← mkNnfIff b false ey]))
  | (``Iff, #[a, b]) =>
    if pol then
      let (e1, e2) ← decompose expandedE ``And
      let (eaF, ebT) ← decompose e1 ``Or
      let (ebF, eaT) ← decompose e2 ``Or
      let step ← mkAppM ``iff_cnf #[a, b]
      ascribe (← mkIffTrans step (← mkAppM ``and_congr
        #[← mkAppM ``or_congr #[← mkNnfIff a false eaF, ← mkNnfIff b true ebT],
          ← mkAppM ``or_congr #[← mkNnfIff b false ebF, ← mkNnfIff a true eaT]]))
    else
      let (e1, e2) ← decompose expandedE ``Or
      let (eaT, ebF) ← decompose e1 ``And
      let (eaF, ebT) ← decompose e2 ``And
      let step ← mkAppM ``not_iff_cnf #[a, b]
      ascribe (← mkIffTrans step (← mkAppM ``or_congr
        #[← mkAppM ``and_congr #[← mkNnfIff a true eaT, ← mkNnfIff b false ebF],
          ← mkAppM ``and_congr #[← mkNnfIff a false eaF, ← mkNnfIff b true ebT]]))
  | (``ite, #[_, c, inst, a, b]) =>
    if pol then
      let (e1, e2) ← decompose expandedE ``And
      let (ecF, eaT) ← decompose e1 ``Or
      let (ecT, ebT) ← decompose e2 ``Or
      -- pin the USER's Decidable instance (Slice-3 review R-ii: the
      -- trailing `[Decidable c]` was left unsynthesized by mkAppM —
      -- binder order is (c a b)[inst]) — a freshly synthesized one
      -- need not be defeq to the user's
      let step ← mkAppOptM ``ite_cnf #[some c, some a, some b, some inst]
      ascribe (← mkIffTrans step (← mkAppM ``and_congr
        #[← mkAppM ``or_congr #[← mkNnfIff c false ecF, ← mkNnfIff a true eaT],
          ← mkAppM ``or_congr #[← mkNnfIff c true ecT, ← mkNnfIff b true ebT]]))
    else
      let (e1, e2) ← decompose expandedE ``Or
      let (ecT, eaF) ← decompose e1 ``And
      let (ecF, ebF) ← decompose e2 ``And
      let step ← mkAppOptM ``not_ite_cnf #[some c, some a, some b, some inst]
      ascribe (← mkIffTrans step (← mkAppM ``or_congr
        #[← mkAppM ``and_congr #[← mkNnfIff c true ecT, ← mkNnfIff a false eaF],
          ← mkAppM ``and_congr #[← mkNnfIff c false ecF, ← mkNnfIff b false ebF]]))
  | _ =>
    if origE.isConstOf ``True then
      if pol then ascribe (← mkAppM ``Iff.refl #[origE])
      else ascribe (← mkAppM ``not_true #[])
    else if origE.isConstOf ``False then
      if pol then ascribe (← mkAppM ``Iff.refl #[origE])
      else ascribe (← mkAppM ``not_false #[])
    else
      match origE.getAppFnArgs with
      | (``Eq, #[ty, a, b]) =>
        match arithTyOf ty with
        | some _ => ascribe (← mkAppM ``Iff.refl #[userSide])
        | none =>
          let inner ← do
            if pol then
              let (e1, e2) ← decompose expandedE ``And
              let (eaF, ebT) ← decompose e1 ``Or
              let (ebF, eaT) ← decompose e2 ``Or
              let step ← mkAppM ``iff_cnf #[a, b]
              mkIffTrans step (← mkAppM ``and_congr
                #[← mkAppM ``or_congr #[← mkNnfIff a false eaF, ← mkNnfIff b true ebT],
                  ← mkAppM ``or_congr #[← mkNnfIff b false ebF, ← mkNnfIff a true eaT]])
            else
              let (e1, e2) ← decompose expandedE ``Or
              let (eaT, ebF) ← decompose e1 ``And
              let (eaF, ebT) ← decompose e2 ``And
              let step2 ← mkAppM ``not_iff_cnf #[a, b]
              mkIffTrans step2 (← mkAppM ``or_congr
                #[← mkAppM ``and_congr #[← mkNnfIff a true eaT, ← mkNnfIff b false ebF],
                  ← mkAppM ``and_congr #[← mkNnfIff a false eaF, ← mkNnfIff b true ebT]])
          let pe ← mkAppM ``prop_eq_iff #[a, b]
          if pol then
            ascribe (← mkIffTrans pe inner)
          else
            ascribe (← mkIffTrans (← mkNotCongr pe) inner)
      | _ => ascribe (← mkAppM ``Iff.refl #[userSide])

/-- The substitution link for a definitional clause: pairs the
normalized clause form with the taut form (= the clause form with the
defined proxy's def inlined), producing
`eval oracle ncf ↔ eval oracle tautF`. Both sides are
polarity-normalized, so non-inlined leaves pair as identical `.lit`s
(possibly under a common `.neg` wrapper). -/
partial def mkDefLink (bctx : BridgeCtx) (p : Nat) (defCore : BoolDef) :
    (ncf tautF : BoolDef) → TacticM Expr
  | .fls, .fls => do
    let e := mkApp2 (mkConst ``BoolDef.eval) bctx.oracleE (boolDefToExpr .fls)
    mkAppM ``Iff.refl #[e]
  | .or a1 b1, .or a2 b2 => do
    let h1 ← mkDefLink bctx p defCore a1 a2
    let h2 ← mkDefLink bctx p defCore b1 b2
    let pf ← mkAppM ``or_congr #[h1, h2]
    let ltE := evalAppE bctx (.or a1 b1)
    let rtE := evalAppE bctx (.or a2 b2)
    mkExpectedTypeHint pf (← mkAppM ``Iff #[ltE, rtE])
  | .neg a1, .neg a2 => do
    let h ← mkDefLink bctx p defCore a1 a2
    let pf ← mkNotCongr h
    let ltE := evalAppE bctx (.neg a1)
    let rtE := evalAppE bctx (.neg a2)
    mkExpectedTypeHint pf (← mkAppM ``Iff #[ltE, rtE])
  | .lit l, t => do
    if l.bvar == p then
      -- the inlined position: t is the proxy's def (native check)
      unless t == defCore do
        throwError "nonlinear_arith: internal: deflink inline mismatch"
      let boundary ← mkProxyBoundary bctx p   -- eval defCore ↔ litHolds ⟨p,false⟩
      let pf ← mkIffSymm boundary             -- litHolds ⟨p,false⟩ ↔ eval defCore
      let ltE := evalAppE bctx (.lit l)
      let rtE := evalAppE bctx t
      mkExpectedTypeHint pf (← mkAppM ``Iff #[ltE, rtE])
    else do
      unless t == .lit l do
        throwError "nonlinear_arith: internal: deflink leaf mismatch"
      let e := evalAppE bctx (.lit l)
      mkAppM ``Iff.refl #[e]
  | _, _ => throwError "nonlinear_arith: internal: deflink shape mismatch"

/-- The definitional-clause bridge: `clauseHolds ρ* atomsE C` from the
taut check of the inline form. -/
def mkDefClauseBridge (bctx : BridgeCtx) (C : List Literal) (p : Nat) : TacticM Expr := do
  let ncf := BoolDef.normNeg (clauseForm C)
  let some (defCore, _) := bctx.proxies[p]?
    | throwError "nonlinear_arith: internal: unregistered proxy {p}"
  let tautF := inlineProxy p defCore ncf
  -- defs are stored normalized; the inline of a normalized form at a
  -- normalized def is normalized (so `taut_sound`'s conclusion is
  -- directly `eval oracle tautF` — the kernel checks this by
  -- computation at ascription)
  unless BoolDef.normNeg defCore == defCore do
    throwError "nonlinear_arith: internal: proxy def not normalized"
  unless BoolDef.normNeg tautF == tautF do
    throwError "nonlinear_arith: internal: taut form not normalized"
  let tautTy ← mkAppM ``Eq #[← mkAppM ``BoolDef.taut #[boolDefToExpr tautF],
    mkConst ``true]
  let tautPrf ← mkDecideProof tautTy
  let sound ← mkAppM ``BoolDef.taut_sound #[tautPrf, bctx.oracleE]
  let link ← mkDefLink bctx p defCore ncf tautF
  let evalNcf ← mkAppM ``Iff.mpr #[link, sound]
  let CE ← Walk.quoteLits C
  let hdecTy ← mkAppM ``Eq #[← mkAppM ``clauseDecodable #[bctx.atomsE, CE],
    mkConst ``true]
  let hdecPrf ← mkDecideProof hdecTy
  let bridge ← mkAppM ``clauseHolds_iff_evalNorm #[bctx.ρStar, bctx.atomsE, CE, hdecPrf]
  mkAppM ``Iff.mpr #[bridge, evalNcf]


/-- The per-literal Iff at the bridge site (dispatches arith vs proxy,
polarity included). -/
def mkLeafIff (bctx : BridgeCtx) (l : Literal) : TacticM Expr := do
  match bctx.atoms[l.bvar]! with
  | some (.ineq _) => mkLitIff bctx l
  | some (.bool _) =>
    let base ← mkProxyIff bctx l.bvar
    if l.neg then mkNotCongr base else pure base
  | _ => throwError "nonlinear_arith: internal: leaf at junk slot {repr l}"

/-- Or-chain witness: position `j` of the clause's eval form from a
`litHolds` proof. Explicit types (Or.inl/inr's implicit `b` can't be
inferred from the proof alone). -/
partial def mkOrWitness (bctx : BridgeCtx) (C : List Literal) (j : Nat)
    (litPf : Expr) : TacticM Expr := do
  match C with
  | [] => throwError "nonlinear_arith: internal: witness position out of range"
  | l₀ :: rest =>
    let ltE := mkApp bctx.oracleE (Refute.litToExpr l₀)
    if j == 0 then
      let rtE := evalAppE bctx (clauseForm rest)
      mkAppOptM ``Or.inl #[none, some rtE, some litPf]
    else
      let inner ← mkOrWitness bctx rest (j - 1) litPf
      let rtE := evalAppE bctx (clauseForm rest)
      mkAppOptM ``Or.inr #[some ltE, none, some inner]

/-- From the fls leaf's user proof to `False`. `ud` is `False` or
`¬True` (the only sources of `.fls` in reifyProp). -/
def mkFlsToFalse (ud : Expr) (h : Expr) : TacticM Expr := do
  if ud.isConstOf ``False then return h
  if ud.isAppOf ``Not then
    -- h : ¬True — apply to True.intro
    return mkApp h (mkConst ``True.intro)
  throwError "nonlinear_arith: internal: fls leaf with unexpected prop {ud}"

/-- Evaluate the elimination plan: from `h` (the current expanded prop)
to a proof of `eval oracleE (clauseForm C)`. -/
partial def buildEvalFromPlan (bctx : BridgeCtx) (C : List Literal) :
    ElimTree → Expr → TacticM Expr
  | .witness l ud, h => do
    let iffE ← mkLeafIff bctx l
    unless (← isDefEq (← inferType h) ud) do
      throwError "nonlinear_arith: internal: plan/user mismatch at {repr l}"
    let litPf ← mkAppM ``Iff.mp #[iffE, h]
    let some j := C.findIdx? (· == l)
      | throwError "nonlinear_arith: internal: witness not in clause"
    let pf ← mkOrWitness bctx C j litPf
    mkExpectedTypeHint pf (evalAppE bctx (clauseForm C))
  | .elimFalse ud, h => do
    let fE ← mkFlsToFalse ud h
    let pf ← mkAppOptM ``False.elim #[some (evalAppE bctx (clauseForm C)), some fE]
    mkExpectedTypeHint pf (evalAppE bctx (clauseForm C))
  | .andL t, h => do buildEvalFromPlan bctx C t (← mkAppM ``And.left #[h])
  | .andR t, h => do buildEvalFromPlan bctx C t (← mkAppM ``And.right #[h])
  | .orE t1 t2, h => do
    let hTy ← inferType h
    let (ua, ub) ← match hTy.getAppFnArgs with
      | (``Or, #[ua, ub]) => pure (ua, ub)
      | _ => throwError "nonlinear_arith: internal: orE on non-Or {hTy}"
    let lamA ← withLocalDecl `ha .default ua fun haE => do
      mkLambdaFVars #[haE] (← buildEvalFromPlan bctx C t1 haE)
    let lamB ← withLocalDecl `hb .default ub fun hbE => do
      mkLambdaFVars #[hbE] (← buildEvalFromPlan bctx C t2 hbE)
    mkAppM ``Or.elim #[h, lamA, lamB]

/-- The root-clause bridge: `clauseHolds ρ* atomsE C` from the source
hypothesis via the NNF Iff + the elimination plan. -/
def mkRootBridge (bctx : BridgeCtx) (e : RootEntry) : TacticM Expr := do
  let nnf ← mkNnfIff e.origE true e.expandedE
  let hExpanded ← mkAppM ``Iff.mp #[nnf, e.hypE]
  let evalPf ← buildEvalFromPlan bctx e.clause e.plan hExpanded
  let CE ← Walk.quoteLits e.clause
  let bridge ← mkAppM ``clauseHolds_iff_eval #[bctx.ρStar, bctx.atomsE, CE]
  mkAppM ``Iff.mpr #[bridge, evalPf]
/-! ## Final assembly -/

/-- The `∀ C ∈ Cs, clauseHolds ρ atoms C` dispatch: a lambda whose body
eliminates the membership Or-chain (List.Mem unfolds to it
definitionally — the `Walk.memChain` idiom in reverse), transporting
the per-clause bridge along the Eq via `congrArg` + `Iff.of_eq`. -/
partial def buildDispatch (bctx : BridgeCtx) (CsE : Expr)
    (CsVals : List (List Literal)) (bridges : List Expr) : MetaM Expr := do
  let listLitTy := mkApp (mkConst ``List [levelZero]) (mkConst ``Literal)
  withLocalDecl `C .default listLitTy fun CE => do
  let memTy ← mkAppM ``Membership.mem #[CsE, CE]
  withLocalDecl `hC .default memTy fun hCE => do
  -- the clauseHolds motive as a lambda (for the Eq transport)
  let motive ← withLocalDecl `Cx .default listLitTy fun CxE => do
    mkLambdaFVars #[CxE] (mkApp3 (mkConst ``clauseHolds) bctx.ρStar bctx.atomsE CxE)
  let rec go (Cs : List (List Literal)) (bs : List Expr) (hCur : Expr) : MetaM Expr := do
    match Cs, bs with
    | [], [] =>
      let goalTy ← mkAppM ``clauseHolds #[bctx.ρStar, bctx.atomsE, CE]
      let pf ← mkAppOptM ``False.elim #[some goalTy,
        some (← mkAppM' (mkConst ``List.not_mem_nil [levelZero]) #[hCur])]
      mkExpectedTypeHint pf goalTy
    | Cᵢ :: Crest, bᵢ :: brest =>
      let headE ← Walk.quoteLits Cᵢ
      let restE ← Walk.quoteLitsList Crest
      let eqTy := mkApp3 (mkConst ``Eq [levelOne]) listLitTy CE headE
      let restMemTy ← mkAppM ``Membership.mem #[restE, CE]
      let goalTy := mkApp3 (mkConst ``clauseHolds) bctx.ρStar bctx.atomsE CE
      let hiLam ← withLocalDecl `hi .default eqTy fun hiE => do
        let cong ← mkAppM ``congrArg #[motive, hiE]
        let iff ← mkAppM ``Iff.of_eq #[cong]
        let tr ← mkAppM ``Iff.mpr #[iff, bᵢ]
        mkLambdaFVars #[hiE] tr
      let restLam ← withLocalDecl `hrest .default restMemTy
        fun hrestE => do mkLambdaFVars #[hrestE] (← go Crest brest hrestE)
      -- the Mem → Or conversion goes through `List.mem_cons` (the
      -- Walk.memChain idiom, elimination direction)
      let memCons ← mkAppOptM ``List.mem_cons
        #[some listLitTy, some headE, some restE, some CE]
      let hOr ← mkAppM ``Iff.mp #[memCons, hCur]
      mkAppOptM ``Or.elim #[some eqTy, some restMemTy, some goalTy,
        some hOr, some hiLam, some restLam]
    | _, _ => throwError "nonlinear_arith: internal: dispatch arity mismatch"
  let body ← go CsVals bridges hCE
  mkLambdaFVars #[CE, hCE] body

/-- Phase 1: reify + clausify all hypotheses (plus the ℕ nonneg
clauses, decision 2 — Verus's own z3 encoding adds 0 ≤ n).

Hyp discipline (nla-15): `strictFvs` (the negated goal `hGN`) reifies
STRICTLY — any failure throws. All other hyps are best-effort: shapes
outside the arithmetic fragment (dependent ∀ — e.g. the ambient axiom
clusters tactus emits into every proof context — ∃, unsupported-type
comparisons, prop applications) are SKIPPED and counted, never
reified. Skipping is sound (weakening) and z3-faithful: the spinoff
query carries those facts too, and nlsat never consumes them (MBQI
off). The classification is BY THE REIFIER'S OWN ERROR, not a
syntactic pre-scan (review R-i: a `mentionsDivMod` pre-scan
misclassified ∀-WRAPPED div/mod hyps — vstd's div/mod lemma shape —
as strict; reifyProp's ∀ arm throws before the div is ever reached, so
only genuinely in-fragment div/mod produces the L1-owned-invariant
error): `L1-owned invariant` (div/mod) and `internal:` (bug
visibility) rethrow; everything else skips. A partially-completed
reify may leave unused var/atom slots behind (z3's created-but-unused
atoms — inert: no clause references them, and the walk's precheck
compares the table against itself). -/
def phase1 (hypFvs : Array FVarId) (strictFvs : Array FVarId) : RM ReifyState := do
  for fv in hypFvs do
    let ty ← instantiateMVars (← fv.getType)
    let strict := strictFvs.contains fv
    try
      let fe ← reifyProp ty true
      clausify (mkFVar fv) ty fe.2 fe id
    catch ex =>
      let msg ← ex.toMessageData.toString
      if strict || msg.containsSubstr "L1-owned invariant"
          || msg.startsWith "nonlinear_arith: internal:" then
        throw ex
      modify fun s => { s with skippedInert := s.skippedInert + 1 }
  for i in [0 : (← get).vars.size] do
    if (← get).varTy[i]! == .nat then
      let nE := (← get).varKeys[i]!
      let zeroN ← mkNumeral (mkConst ``Nat) 0
      let origE ← mkAppM ``GE.ge #[nE, zeroN]
      let lit ← reifyCmp .ge nE zeroN origE .nat true
      let hypE ← mkAppM ``Nat.zero_le #[nE]
      let some info := (← get).litProps[lit]?
        | throwError "nonlinear_arith: internal: nat clause unregistered"
      modify fun s => { s with roots := s.roots.push (⟨[lit], hypE, origE, origE, .witness lit info.userSide⟩) }
  get

/-- Which bridge a selected clause gets (Slice 3: the post-run clause
selection mixes definitional and root clauses in referenced-cid order). -/
inductive ClauseSrc where
  | defClause (p : Nat)
  | root (e : RootEntry)

/-- The shared prelude: `True` short-circuit (goal closed, returns
`none`), `byContradiction` + intro of the negated goal, then phase 1
(reify + Tseitin clausify). Returns the `False`-goal mvar and the
reify state for the phase-2/orchestration consumer. The target is
mdata-stripped FIRST (nla-15: a preceding `have` wraps the goal in
`noImplicitLambda` mdata — without `consumeMData` the short-circuit
never fires in tactic-composed contexts, and the mdata leaks into
hGN's type). -/
def prelude : TacticM (Option (MVarId × ReifyState)) := do
  let g ← getMainGoal
  let target := (← instantiateMVars (← g.getType)).consumeMData
  if target.isConstOf ``True then
    g.assign (mkConst ``True.intro)
    replaceMainGoal []
    return none
  let (gFalse, strictFvs) ←
    if target.isConstOf ``False then pure (g, #[])
    else do
      let [g'] ← g.apply (mkConst ``Classical.byContradiction)
        | throwError "nonlinear_arith: internal: byContradiction shape"
      let (hgn, g'') ← g'.intro `hGN
      pure (g'', #[hgn])
  gFalse.withContext (n := TacticM) do
    -- phase 1: reify + clausify all hyps (hGN included — its `Not` flips
    -- to the goal at negative polarity inside reifyProp — and STRICT:
    -- the goal itself must always reify; other hyps may be skipped as
    -- inert, see phase1)
    let hypFvs ← gFalse.getNondepPropHyps
    let st ← (phase1 hypFvs strictFvs).run' {}
    return some (gFalse, st)

/-- Phase 2 + final assembly, parameterized on the atom table, the
internal→external variable permutation, and the clause selection
(Slice-2 dev path: `st.atoms`, the identity, ALL def+root clauses in
emission order; Slice-3 orchestrate path: the patched snapshot table,
the reorder capture, the referenced inputs in cid order with
solver-sorted literal lists). Builds the per-clause bridges, the
dispatch, the integrality witnesses and the refutation goal type;
assigns `gFalse` and returns the refutation-goal mvar.

`perm` maps INTERNAL (snapshot/goal `ρ`) indices to external
(`st.vars`) slots — after `Solver.heuristicReorder`, `s.perm` is
exactly this (verified in `Solver.reorder`'s remap: post-reorder
`perm[internal] = external`; identity when no reorder ran). -/
def assembleRefutation (gFalse : MVarId) (st : ReifyState)
    (atomsV : Array (Option Atom)) (perm : Array Var)
    (cls : List (List Literal × ClauseSrc)) : TacticM MVarId := do
  gFalse.withContext (n := TacticM) do
    -- phase 2: bridges (against the GIVEN table + permuted ρ*)
    let atomsE ← atomsToExpr atomsV
    let valsI := (List.range st.vars.size).toArray.map fun i => st.vars[perm[i]!]!
    let ρStarE ← rhoStarExpr valsI
    let hordTy ← mkAppM ``Eq #[← mkAppM ``boolDefsOrdered #[atomsE], mkConst ``true]
    let hordPrf ← mkDecideProof hordTy
    let oracleE := mkApp2 (mkConst ``litHolds) ρStarE atomsE
    let litCache ← IO.mkRef ({} : Std.HashMap Literal Expr)
    let proxyCache ← IO.mkRef ({} : Std.HashMap Nat Expr)
    let bctx : BridgeCtx :=
      { ρStar := ρStarE, atomsE, atoms := atomsV, hordPrf, oracleE,
        litProps := st.litProps, proxies := st.proxies,
        litCache, proxyCache }
    let bridges ← cls.mapM fun (C, src) =>
      match src with
      | .defClause p => mkDefClauseBridge bctx C p
      | .root e => mkRootBridge bctx { e with clause := C }
    let CsVals := cls.map (·.1)
    let CsE ← Walk.quoteLitsList CsVals
    let dispatch ← buildDispatch bctx CsE CsVals bridges
    -- integrality witnesses (12e decision 1: per ℤ/ℕ slot, ahead of the
    -- clause hyp in the refutation goal; internal slot i ↔ external
    -- var perm[i])
    let intWits ← (List.range st.vars.size).filterMapM fun i =>
      let ext := perm[i]!
      match st.varTy[ext]! with
      | .real => pure none
      | ty => do
        let srcE := st.varKeys[ext]!
        let valE := st.vars[ext]!
        -- the ∃ predicate `fun n : ℤ => ρ* i = ↑n`
        let predLam ← withLocalDecl `n .default (mkConst ``Int) fun nE => do
          let eqTy ← mkAppM ``Eq #[mkApp ρStarE (toExpr i),
          ← mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some nE]]
          mkLambdaFVars #[nE] eqTy
        let eqPrf ← do
          match ty with
          | .int =>
            -- ρ* i = ↑srcE by ρ*'s reduction (valE = Int.cast srcE)
            let tgt ← mkAppM ``Eq #[mkApp ρStarE (toExpr i), valE]
            mkExpectedTypeHint (← mkEqRefl valE) tgt
          | .nat =>
            -- ρ* i = ↑(↑srcE : ℤ) via Int.cast_natCast — R pinned
            -- explicit (Slice-3 review R-ii: binders are
            -- {R} [AddGroupWithOne R] (n) — mkAppM can't synthesize the
            -- instance with ?R still a mvar)
            let wE ← mkAppOptM ``Nat.cast #[some (mkConst ``Int), none, some srcE]
            let prf ← mkAppM ``Eq.symm #[← mkAppOptM ``Int.cast_natCast
              #[some (mkConst ``Real), none, some srcE]]
            let tgt ← mkAppM ``Eq #[mkApp ρStarE (toExpr i),
              ← mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some wE]]
            mkExpectedTypeHint prf tgt
          | .real => throwError "nonlinear_arith: internal: real slot in intWits"
        let witE ← match ty with
          | .int => pure srcE
          | .nat => mkAppOptM ``Nat.cast #[some (mkConst ``Int), none, some srcE]
          | .real => throwError "nonlinear_arith: internal: real slot in intWits"
        let w ← mkAppOptM ``Exists.intro #[none, some predLam, some witE, some eqPrf]
        pure (some w)
    -- the refutation goal type
    let refTy ← withLocalDecl `ρ .default (← mkArrow (mkConst ``Nat) (mkConst ``Real))
      fun ρE => do
      let clauseHypTy ← withLocalDecl `C .default
        (mkApp (mkConst ``List [levelZero]) (mkConst ``Literal)) fun CE => do
        let memTy ← mkAppM ``Membership.mem #[CsE, CE]
        let chTy := mkApp3 (mkConst ``clauseHolds) ρE atomsE CE
        mkForallFVars #[CE] (← mkArrow memTy chTy)
      let mut ty ← mkArrow clauseHypTy (mkConst ``False)
      for i in (List.range st.vars.size).reverse do
        match st.varTy[perm[i]!]! with
        | .real => pure ()
        | _ =>
          let intHypTy ← withLocalDecl `n .default (mkConst ``Int) fun nE => do
            let eqTy ← mkAppM ``Eq #[mkApp ρE (toExpr i),
            ← mkAppOptM ``Int.cast #[some (mkConst ``Real), none, some nE]]
            let lam ← mkLambdaFVars #[nE] eqTy
            mkAppM ``Exists #[lam]
          ty ← pure (← mkArrow intHypTy ty)
      mkForallFVars #[ρE] ty
    let m ← mkFreshExprMVar refTy
    let appArgs := #[ρStarE] ++ intWits.toArray ++ #[dispatch]
    gFalse.assign (mkAppN m appArgs)
    return m.mvarId!

/-- The Slice-2 deliverable (see the module doc): reduce the main goal
`Γ ⊢ G` to the walk's refutation goal
`∀ ρ, (integrality hyps) → (∀ C ∈ Cs, clauseHolds ρ atoms C) → False`,
left as the new main goal (Slice 3 closes it via solver + walk). -/
def toRefutationGoal : TacticM Unit := do
  if let some (gFalse, st) ← prelude then
    let cls := (st.defClauses.toList.map fun (C, p) => (C, ClauseSrc.defClause p))
      ++ (st.roots.toList.map fun e => (e.clause, ClauseSrc.root e))
    let m ← assembleRefutation gFalse st st.atoms (Array.range st.vars.size) cls
    replaceMainGoal [m]

/- The walk's referenced-input contract is computed by
`Walk.referencedInputCids` (single source, shared with `precheck` and
`walkRefutation` — Slice-3 review R-i). -/

/-- L2-invocation counter / last-run conflict count (Slice 4) — bumped
inside `orchestrate`, reported by `nonlinear_arith_stats`; the counter
backs the L1-never-touches-L2 pin. Entry semantics: the bump is at
orchestrate's ENTRY (L2 entered — incl. prelude-failure exits), and the
conflict count is zeroed there and set for real after the solver run,
so a short-circuit exit never reports a stale count. -/
initialize nlaL2Runs : IO.Ref Nat ← IO.mkRef 0
initialize nlaL2Conflicts : IO.Ref Nat ← IO.mkRef 0

/-- How an `orchestrate` run closed the goal (Slice-4 review R-i:
stats exactness). `prelude` = the True short-circuit fired before any
solver work; `refuted` = the full search → trace → walk pipeline ran
(SAT/undef exits throw). -/
inductive OrchestrateExit | prelude | refuted

/-- Slice 3: reify → register → solve → patch → bridge → walk,
end-to-end. On UNSAT the original goal is closed by the walked
refutation; on SAT a per-var model display fails the tactic (decision
4 — never a wrong close); on undef a bounded-exit error names the
gate. -/
unsafe def orchestrate : TacticM OrchestrateExit := do
  nlaL2Runs.modify (· + 1)
  nlaL2Conflicts.set 0
  let some (gFalse, st) ← prelude | return .prelude
  -- W3: registration (SolverM is exception-free — alignment is asserted
  -- on the post-registration state below, in TacticM)
  let reg : SolverM Unit := do
    Solver.init
    for i in [0:st.vars.size] do
      let _ ← Solver.mkVar (st.varTy[i]! != .real)
    for slot in [1:st.atoms.size] do
      match st.atoms[slot]! with
      | some (.ineq ia) => let _ ← Solver.mkIneqAtom ia
      | some (.bool _) => let _ ← Solver.mkBoolVar
      -- unreachable: the frontend never emits root atoms, and slot 0 is
      -- the only `none` (the true-bvar reservation, created by `init`)
      | _ => pure ()
    for (C, _) in st.defClauses do
      let _ ← Solver.mkClause C.toArray false
    for e in st.roots do
      let _ ← Solver.mkClause e.clause.toArray false
  let ((), sReg) := reg.run Solver.empty
  -- hash-cons collapse guard (mkIneqAtom dedups structurally — the
  -- frontend's arithMap should already prevent it; fail loud if not)
  unless sReg.isInt.size == st.vars.size && sReg.atoms.size == st.atoms.size &&
      sReg.clauses.size == 1 + st.defClauses.size + st.roots.size do
    throwError "nonlinear_arith: internal: solver registration misaligned \
      ({sReg.isInt.size} vars vs {st.vars.size}, {sReg.atoms.size} atoms vs \
      {st.atoms.size}, {sReg.clauses.size} clauses vs \
      {1 + st.defClauses.size + st.roots.size})"
  for slot in [1:st.atoms.size] do
    unless (sReg.atoms[slot]! == st.atoms[slot]! ||
        (st.atoms[slot]! matches some (.bool _)) && sReg.atoms[slot]!.isNone) do
      throwError "nonlinear_arith: internal: atom slot {slot} misaligned after registration"
  let ((r, perm), sFin) :=
    (Solver.checkCapturing (Solver.resolve Explain.explain)).run sReg
  nlaL2Conflicts.set sFin.conflicts
  match r with
  | some .false =>
    let some snap := sFin.refutation
      | throwError "nonlinear_arith: internal: UNSAT exit without a refutation snapshot"
    let (snapAtoms, snapClauses, snapBundles, snapFinal) := snap
    -- W4: patch the proxy defs into the snapshot's atom table
    -- (bvar-keyed — heuristicReorder never permutes bvar slots), and
    -- rebuild Cs to the REFERENCED bundle-less inputs (precheck's
    -- contract), with the solver-sorted literal lists.
    let mut patched := snapAtoms
    for (p, (defCore, _)) in st.proxies.toArray do
      patched := patched.set! p (some (.bool defCore))
    let refCids := Walk.referencedInputCids snapBundles snapFinal
    let cls ← refCids.toList.mapM fun cid => do
      if cid == 0 then
        throwError "nonlinear_arith: trace references the true-bvar clause \
          (cid 0) — unsupported (pin: never observed)"
      let C := snapClauses[cid]!.lits.toList
      let fidx := cid - 1
      if fidx < st.defClauses.size then
        pure (C, ClauseSrc.defClause st.defClauses[fidx]!.2)
      else
        let some e := st.roots[fidx - st.defClauses.size]?
          | throwError "nonlinear_arith: internal: referenced cid {cid} out of range"
        pure (C, ClauseSrc.root e)
    let m ← assembleRefutation gFalse st patched perm cls
    let snapE ← Quote.snapshotToExpr (patched, snapClauses, snapBundles, snapFinal)
    replaceMainGoal [m]
    Walk.walkRefutation (← getMainGoal) snapE
  | some .true =>
    -- decision 4: per-var model display off the post-restore (external
    -- order) assignment. Proxy bvars carry no assignment — skipped by
    -- construction.
    let mut lines : Array MessageData := #[]
    for (x, cid) in sFin.assignment do
      if x < st.varKeys.size then
        let key := st.varKeys[x]!
        let vStr : String := match sFin.store[cid]! with
          | .rat q => toString q
          | v@(.root ..) =>
            match Kernel.RAlg.refineUntilPrec v 10 with
            | .rat q => toString q
            | .root p a b _ => s!"root of {repr p} in [{a}, {b}]"
        lines := lines.push m!"  {key} := {vStr}"
    let intNote : MessageData :=
      if st.varTy.any (· != .real) then
        m!"\n(note: the model is over ℝ — it need not specialize to the integer-valued vars)"
      else m!""
    let skipNote : MessageData :=
      if st.skippedInert == 1 then
        m!"\n(note: 1 hypothesis outside the arithmetic fragment was ignored — it may rule this model out)"
      else if st.skippedInert > 1 then
        m!"\n(note: {st.skippedInert} hypotheses outside the arithmetic fragment were ignored — they may rule this model out)"
      else m!""
    throwError "nonlinear_arith: satisfiable — the negated goal has a model, \
      so the goal is not provable:{intNote}{skipNote}\n{MessageData.joinSep lines.toList "\n"}"
  | _ =>
    throwError "nonlinear_arith: nlsat search exited undef (fragment gate or bound)"
  return .refuted

/-- Debug/dev entry: `nla_frontend` runs the Slice-2 transform, leaving
the refutation goal (close it by hand or `nlsat_refute` in pins). -/
elab "nla_frontend" : tactic => toRefutationGoal

/-- Dev entry for Slice 3: `nla_solve` runs reify → solve → quote →
walk end-to-end (no hand-written snapshot). -/
elab "nla_solve" : tactic => unsafe (do let _ ← orchestrate)

/-! ## nla-14 Slice 4 — the `nonlinear_arith` elab + L1/L2 layering

DESIGN-endgame §2.7's verbatim shape: a sandboxed L1 fast path
(`saturateCore`); on ANY failure roll back to the ORIGINAL goal and run
L2 (`orchestrate`); each layer under its own fresh user budget
(`withLayerHeartbeats` — the BUDGET-SHAPE lesson: per-layer fresh
scopes, never fraction-of-remaining). The sandbox idiom is
tryGrobner's (Saturate.lean:1899-1904): saveState + tryCatchRuntimeEx
+ restoreState — the restore wipes both L1's context/env churn
(ring_nf'd hyps, noted facts) and its failure messages, so L2's
prelude sees the user's original goal. -/

/-- nla-16 parity-harness channel (Slice 0): when the spawned lean process
carries `NLA16_STATS=1` in its environment, every successful close emits a
single `[nla16-stats] <payload>` WARNING line. Warning severity is
deliberate: verus's per-fn lean checker forwards diagnostics of severity
`warning` on CheckResult::Success even for verified fns
(`verifier.rs:2489`), while info diagnostics are dropped — so warning is
the only channel that reaches the verus log on green runs. Default-off
(the env var is absent in normal runs; no verus-side change needed). The
gate is on the VALUE `1` exactly (presence alone is not enough — POSIX has
no unset-via-set, IO.setEnv with "" otherwise stays armed).
Sandbox note: the L1 attempt's message log is restored on rollback, so a
stats line can only survive on an actual close — exactly the census
semantics (`layer=1` ⇒ L1 closed; `layer=2-…` ⇒ L2; absent ⇒ this arm
failed and the ladder's fallback closed). -/
unsafe def reportStats (payload : String) : TacticM Unit := do
  if (← IO.getEnv "NLA16_STATS") == some "1" then
    logWarning s!"[nla16-stats] {payload}"

/-- The §2.7 layering driver. L1's failure is exception-shaped (the
tier-2 omega leaf is deliberately unwrapped, Saturate.lean:2031), so a
normal return means the goal it worked on closed; the `g0.isAssigned`
check is the defensive cover for saturateCore's goal-agnostic early
returns (a throw there falls through to L2, which is the safe side).
Known edge (considered-not-engineered, Slice-4 plan): `ring_nf at *`
can close g0 outright, after which saturateCore works on the NEXT goal;
a throw there resurrects g0 via the rollback and L2 closes it —
correct, at worst redundant. -/
unsafe def nonlinearArithCore (stats : Bool) (maxRounds : Option Nat) :
    TacticM Unit := do
  let g0 ← getMainGoal
  let s ← saveState
  let l1 ← tryCatchRuntimeEx
    (do Tactic.withLayerHeartbeats
          (Tactic.saturateCore (stats := stats) (maxRounds := maxRounds))
        unless ← g0.isAssigned do
          throwError "nonlinear_arith: internal: L1 returned without closing the goal"
        pure true)
    (fun _ => do restoreState s; pure false)
  if l1 then
    if stats then logInfo "nonlinear_arith: closed by L1 (saturate)"
    reportStats "layer=1"
  else
    let exit ← Tactic.withLayerHeartbeats orchestrate
    if stats then
      match exit with
      | .prelude =>
        logInfo "nonlinear_arith: L1 failed to close the goal; closed by \
          L2's prelude (True goal — no solver work)"
      | .refuted =>
        logInfo s!"nonlinear_arith: L1 failed to close the goal; closed by L2 \
          (nlsat search → trace → kernel-checked walk, {← nlaL2Conflicts.get} conflicts)"
    match exit with
    | .prelude => reportStats "layer=2-prelude"
    | .refuted => reportStats s!"layer=2 conflicts={← nlaL2Conflicts.get}"

/-- `nonlinear_arith (n)?` — the user-facing layered closer (nla-14):
L1 `nla_saturate` fast path (most goals), on failure L2's nlsat
search → trace → kernel-checked walk. The optional numeral overrides
L1's round bound (default: depth-adaptive). Each layer runs under its
own fresh user heartbeat budget (`withLayerHeartbeats`). -/
elab "nonlinear_arith" n:(num)? : tactic =>
  unsafe (do nonlinearArithCore false (n.map (·.getNat)))

/-- `nonlinear_arith_stats (n)?` — the layered closer with L1's phase
timings/counters plus the closing layer and L2's conflict count. -/
elab "nonlinear_arith_stats" n:(num)? : tactic => unsafe (do
  Tactic.nlaLitFast.set 0; Tactic.nlaCacheHit.set 0; Tactic.nlaTacticCall.set 0
  nlaL2Runs.set 0; nlaL2Conflicts.set 0
  nonlinearArithCore true (n.map (·.getNat)))

