import LeanNonlinearArith.Nlsat.Walk

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

The deliverable is `toRefutationGoal`: the main goal `Γ ⊢ G` becomes
`⊢ ∀ ρ, (integrality hyps) → (∀ C ∈ Cs, clauseHolds ρ atoms C) → False`
— the exact shape `Walk.walkRefutation` consumes (Slice 3 runs the
solver and walks; Slice-2 pins close the refutation goal by hand).
-/

namespace LeanNonlinearArith.Nlsat.Frontend

open Lean Meta Elab Tactic
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Check

/-! ## Quoting (shared with Slice 3) -/

/-- Quote an `IneqKind`. -/
def ineqKindToExpr : IneqKind → Expr
  | .eq => mkConst ``IneqKind.eq
  | .lt => mkConst ``IneqKind.lt
  | .gt => mkConst ``IneqKind.gt

/-- Quote a `BoolDef` (recursive). -/
partial def boolDefToExpr : BoolDef → Expr
  | .lit l => mkApp (mkConst ``BoolDef.lit) (Refute.litToExpr l)
  | .and a b => mkApp2 (mkConst ``BoolDef.and) (boolDefToExpr a) (boolDefToExpr b)
  | .or a b => mkApp2 (mkConst ``BoolDef.or) (boolDefToExpr a) (boolDefToExpr b)
  | .neg a => mkApp (mkConst ``BoolDef.neg) (boolDefToExpr a)
  | .tru => mkConst ``BoolDef.tru
  | .fls => mkConst ``BoolDef.fls

/-- Quote an `Atom` (structure-ctor applications — defeq to any
elaboration spelling). -/
def atomToExpr : Atom → Expr
  | .ineq a => mkApp (mkConst ``Atom.ineq)
      (mkApp2 (mkConst ``IneqAtom.mk) (ineqKindToExpr a.kind) (toExpr a.factors))
  | .root a => mkApp (mkConst ``Atom.root)
      (mkApp4 (mkConst ``RootAtom.mk) (Refute.rootKindToExpr a.kind)
        (toExpr a.x) (toExpr a.i) (toExpr a.p))
  | .bool d => mkApp (mkConst ``Atom.bool) (boolDefToExpr d)

/-- Quote an `Option Atom`. -/
def optAtomToExpr : Option Atom → Expr
  | none => mkApp (mkConst ``Option.none [levelZero]) (mkConst ``Atom)
  | some a => mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``Atom) (atomToExpr a)

/-- Quote the atom table (`Array (Option Atom)` via `List.toArray`). -/
def atomsToExpr (atoms : Array (Option Atom)) : MetaM Expr := do
  let elemTy := mkApp (mkConst ``Option [levelZero]) (mkConst ``Atom)
  let listE ← mkListLit elemTy (atoms.toList.map optAtomToExpr)
  mkAppM ``List.toArray #[listE]

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

/-- A comparison, decoded for the bridge chains. -/
structure CmpInfo where
  a : Expr          -- source-level operands
  b : Expr
  ty : ArithTy
  ck : CmpKind
  /-- the user-side proposition (polarity-folded: the reified literal
  bridges THIS, e.g. `¬(a < b)` for a negated literal) -/
  userSide : Expr

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
  /-- definitional clauses: (clause, defined proxy, taut form). -/
  defClauses : Array (List Literal × Nat × BoolDef) := #[]
  /-- root clauses: (clause, source hyp proof expr, elim plan). -/
  roots : Array (List Literal × Expr × ElimTree) := #[]
  /-- ℕ slots get a `0 ≤ ↑n` clause: (bvar of the lt-atom literal). -/
  natClauses : Array (List Literal × Expr × ElimTree) := #[]

abbrev RM := StateT ReifyState TacticM

/-- The arith type of a source expr, if ℤ/ℕ/ℝ. -/
def arithTyOf (tyE : Expr) : Option ArithTy :=
  if tyE.isConstOf ``Int then some .int
  else if tyE.isConstOf ``Nat then some .nat
  else if tyE.isConstOf ``Real then some .real
  else none

/-- The ℝ-level value expr for a source expr of the given type. -/
def toRealExpr (e : Expr) : ArithTy → MetaM Expr
  | .int => mkAppM ``Int.cast #[e]
  | .nat => mkAppM ``Nat.cast #[e]
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

/-- The six comparison forms over the difference poly. -/
inductive CmpKind | lt | le | gt | ge | eq | ne deriving BEq

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
    litProps := s.litProps.insert lit { a, b, ty, ck, userSide } }
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
polarity. Unsupported shapes fail loudly. -/
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

/-- Fresh proxy for a connective form whose children are already
literals: registers the def + definitional clauses (the taut forms
inline the proxy's own def ONE level — children stay abstract, so
checks are local; design review R-i). Returns the positive literal. -/
def mkProxy (defCore : BoolDef) (ud : Expr) : RM Literal := do
  let p := (← get).atoms.size
  match defCore with
  | .and (.lit la) (.lit lb) =>
    modify fun s => { s with
      atoms := s.atoms.push (some (.bool defCore)),
      proxies := s.proxies.insert p (defCore, ud),
      defClauses := s.defClauses
        |>.push ([⟨p, true⟩, la], p, .or (.neg defCore) (.lit la))
        |>.push ([⟨p, true⟩, lb], p, .or (.neg defCore) (.lit lb))
        |>.push ([⟨p, false⟩, la.negate, lb.negate], p,
            .or defCore (.or (.neg (.lit la)) (.neg (.lit lb)))) }
    return ⟨p, false⟩
  | .or (.lit la) (.lit lb) =>
    modify fun s => { s with
      atoms := s.atoms.push (some (.bool defCore)),
      proxies := s.proxies.insert p (defCore, ud),
      defClauses := s.defClauses
        |>.push ([⟨p, true⟩, la, lb], p,
            .or (.neg defCore) (.or (.lit la) (.lit lb)))
        |>.push ([⟨p, false⟩, la.negate], p, .or defCore (.neg (.lit la)))
        |>.push ([⟨p, false⟩, lb.negate], p, .or defCore (.neg (.lit lb))) }
    return ⟨p, false⟩
  | _ => throwError "nonlinear_arith: internal: proxy def not a binary connective"

/-- Tseitin-lift a form to a single literal, proxying connectives
(children first — emission order = the `boolDefsOrdered` invariant). -/
partial def tseitinLit (fe : FormE) : RM Literal := do
  match fe with
  | (.lit l, _) => return l
  | (.and fa fb, ud) =>
    let (_, ua, ub) := ← match ud.getAppFnArgs with
      | (``And, #[ua, ub]) => pure ((), ua, ub)
      | _ => throwError "nonlinear_arith: internal: and-form with non-And user prop {ud}"
    let la ← tseitinLit (fa, ua)
    let lb ← tseitinLit (fb, ub)
    mkProxy (.and (.lit la) (.lit lb)) ud
  | (.or fa fb, ud) =>
    let (_, ua, ub) := ← match ud.getAppFnArgs with
      | (``Or, #[ua, ub]) => pure ((), ua, ub)
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
partial def clausify (hypE : Expr) (fe : FormE) (wrap : ElimTree → ElimTree) :
    RM Unit := do
  match fe with
  | (.and fa fb, ud) =>
    match ud.getAppFnArgs with
    | (``And, #[ua, ub]) =>
      clausify hypE (fa, ua) (fun t => wrap (.andL t))
      clausify hypE (fb, ub) (fun t => wrap (.andR t))
    | _ => throwError "nonlinear_arith: internal: and-form with non-And prop {ud}"
  | (.or _ _, ud) =>
    unless formHasTru fe.1 do
      let (lits, plan) ← orCollect fe
      modify fun s => { s with roots := s.roots.push (lits, hypE, wrap plan) }
  | (.lit l, ud) =>
    modify fun s => { s with roots := s.roots.push ([l], hypE, wrap (.witness l ud)) }
  | (.tru, _) => pure ()
  | (.fls, ud) =>
    modify fun s => { s with roots := s.roots.push ([], hypE, wrap (.elimFalse ud)) }
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
    tryCatchRuntimeEx
      (do
        evalTactic (← `(tactic| simp [Check.evalP, Check.evalM]))
        evalTactic (← `(tactic| push_cast))
        evalTactic (← `(tactic| ring))
        let pf ← instantiateMVars m
        if pf.hasMVar then return none
        return some pf)
      (fun _ => return none)
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
    let fsE := toExpr [(p, false)]
    let atomE := mkApp2 (mkConst ``IneqAtom.mk) (ineqKindToExpr ia.kind) fsE
    mkAppM lem #[bctx.ρStar, atomE]
  let castLinkLt (x y : Expr) : MetaM Expr :=
    match info.ty with
    | .int => mkAppM ``Int.cast_lt #[x, y]
    | .nat => mkAppM ``Nat.cast_lt #[x, y]
    | .real => do mkAppM ``Iff.refl #[← mkAppM ``LT.lt #[x, y]]
  let castLinkLe (x y : Expr) : MetaM Expr :=
    match info.ty with
    | .int => mkAppM ``Int.cast_le #[x, y]
    | .nat => mkAppM ``Nat.cast_le #[x, y]
    | .real => do mkAppM ``Iff.refl #[← mkAppM ``LE.le #[x, y]]
  let castLinkEq (x y : Expr) : MetaM Expr :=
    match info.ty with
    | .int => mkAppM ``Int.cast_eq #[x, y]
    | .nat => mkAppM ``Nat.cast_inj #[x, y]
    | .real => do mkAppM ``Iff.refl #[← mkAppM ``Eq #[x, y]]
  -- pieces of the positive chain: c1 = cast link, c2 = sub-shift,
  -- c3 = align, c4 = holds_single
  let (c1, c2, c3, c4) ← do
    match ia.kind with
    | .lt =>
      return (← castLinkLt info.a info.b, ← mkAppM ``sub_lt_zero #[castA, castB],
        ← mkC3 ``LT.lt false, ← holdsSingle ``holds_single_lt)
    | .gt =>
      return (← castLinkLt info.b info.a, ← mkAppM ``sub_pos #[castA, castB],
        ← mkC3 ``LT.lt true, ← holdsSingle ``holds_single_gt)
    | .eq =>
      return (← castLinkEq info.a info.b, ← mkAppM ``sub_eq_zero #[castA, castB],
        ← mkC3 ``Eq false, ← holdsSingle ``holds_single_eq)
  -- posChain: userPlus ↔ litHolds ⟨b,false⟩ (assembled from the user side)
  let posChain ← mkIffTrans (← mkIffSymm c1) (← mkIffTrans (← mkIffSymm c2)
    (← mkIffTrans (← mkIffSymm c3) (← mkIffSymm c4)))
  -- tailChain: (cast-level positive) ↔ litHolds ⟨b,false⟩
  let tailChain ← mkIffTrans (← mkIffSymm c2)
    (← mkIffTrans (← mkIffSymm c3) (← mkIffSymm c4))
  let full : Expr ← match info.ck, lit.neg with
    | _, false => posChain
    | .lt, true | .eq, true | .gt, true => mkNotCongr posChain
    | .le, true =>
      let t1 ← mkIffSymm (← castLinkLe info.a info.b)
      let t2 ← mkIffSymm (← mkAppM ``not_lt #[castB, castA])
      mkIffTrans t1 (← mkIffTrans t2 (← mkNotCongr tailChain))
    | .ge, true =>
      let t1 ← mkIffSymm (← castLinkLe info.b info.a)
      let t2 ← mkIffSymm (← mkAppM ``not_lt #[castA, castB])
      mkIffTrans t1 (← mkIffTrans t2 (← mkNotCongr tailChain))
    | .le, false =>
      let t1 ← mkIffSymm (← castLinkLe info.a info.b)
      let t2 ← mkIffSymm (← mkAppM ``not_lt #[castB, castA])
      mkNotCongr (← mkIffTrans t1 (← mkIffTrans t2 (← mkNotCongr tailChain)))
    | .ge, false =>
      let t1 ← mkIffSymm (← castLinkLe info.b info.a)
      let t2 ← mkIffSymm (← mkAppM ``not_lt #[castA, castB])
      mkNotCongr (← mkIffTrans t1 (← mkIffTrans t2 (← mkNotCongr tailChain)))
  -- (the CmpKind.ne case shares .eq's atom with baseNeg — covered by the
  -- (_, false)/(_, true) split via posChain/not_congr)
  let litE := Refute.litToExpr lit
  let targetRhs ← mkAppM ``litHolds #[bctx.ρStar, bctx.atomsE, litE]
  let targetTy ← mkAppM ``Iff #[info.userSide, targetRhs]
  let result ← mkExpectedTypeHint full targetTy
  bctx.litCache.modify (·.insert lit result)
  return result

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
    match bctx.atoms.get! l.bvar with
    | some (.bool _) =>
      let base ← mkProxyIff bctx l.bvar
      let pf ← if l.neg then mkNotCongr base else pure base
      ascribe pf
    | some (.ineq _) => ascribe (← mkLitIff bctx l)
    | _ => throwError "nonlinear_arith: internal: leaf at junk slot {repr l}"
  | .and a b =>
    let (_, ua, ub) := ← match expandedE.getAppFnArgs with
      | (``And, #[ua, ub]) => pure ((), ua, ub)
      | _ => throwError "nonlinear_arith: internal: and-form, non-And expanded {expandedE}"
    ascribe (← mkAppM ``and_congr #[← mkFormIff bctx a ua, ← mkFormIff bctx b ub])
  | .or a b =>
    let (_, ua, ub) := ← match expandedE.getAppFnArgs with
      | (``Or, #[ua, ub]) => pure ((), ua, ub)
      | _ => throwError "nonlinear_arith: internal: or-form, non-Or expanded {expandedE}"
    ascribe (← mkAppM ``or_congr #[← mkFormIff bctx a ua, ← mkFormIff bctx b ub])
  | .neg a =>
    let (_, ua) := ← match expandedE.getAppFnArgs with
      | (``Not, #[ua]) => pure ((), ua)
      | _ => throwError "nonlinear_arith: internal: neg-form, non-Not expanded {expandedE}"
    ascribe (← mkNotCongr (← mkFormIff bctx a ua))
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
    let lhs ← mkAppM ``Array.getElem? #[bctx.atomsE, toExpr p]
    let inner := mkApp2 (mkConst ``Option.some [levelZero]) (mkConst ``Atom) defE
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
