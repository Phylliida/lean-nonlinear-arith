import LeanNonlinearArith.Nlsat.Refute

/-!
# nla-14 Slice 3 — Expr quoters for the refutation snapshot

MetaM Expr-builders covering the full refutation grammar (the DumpPP
printer of `scratch_dump.lean` is the syntax-side analogue): literals
(`Refute.litToExpr`, pre-existing), atoms incl. the `.bool` proxy arm
(moved here from the Slice-2 frontend), clauses, all nine `TraceStep`
arms (incl. `pseudoDivision`'s 7 fields and `intBranch (x, lo)`),
bundles, and the `SnapshotTy` payload itself.

MPoly/Int/Nat/Bool/Option/Prod/List quote via core `toExpr` (MPoly is
an abbrev for `List (Int × Monomial)` — the Refute.lean idiom);
`Array`s go through the `List.toArray` idiom (`atomsToExpr`). No `Rat`
appears anywhere in `TraceStep`/`TraceBundle`/`Clause`/`Atom`.

All untrusted meta code: the kernel re-checks every quoted term when
the walk evals and discharges it.
-/

namespace LeanNonlinearArith.Nlsat.Quote

open Lean Meta
open LeanNonlinearArith.Nlsat

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

/-- The `Option Atom` type expression. -/
def optAtomE : Expr := mkApp (mkConst ``Option [levelZero]) (mkConst ``Atom)

/-- Quote an `Array` via `List.toArray` over a `mkListLit` list (the
`atomsToExpr` idiom — defeq to any elaboration spelling). -/
def arrToExpr (elemTy : Expr) (xs : List Expr) : MetaM Expr := do
  mkAppM ``List.toArray #[← mkListLit elemTy xs]

/-- Quote the atom table (`Array (Option Atom)`). -/
def atomsToExpr (atoms : Array (Option Atom)) : MetaM Expr :=
  arrToExpr optAtomE (atoms.toList.map optAtomToExpr)

/-- Quote an `Array Literal`. -/
def litsArrToExpr (lits : Array Literal) : MetaM Expr :=
  arrToExpr (mkConst ``Literal) (lits.toList.map Refute.litToExpr)

/-- Quote an `Array MPoly`. -/
def mpolyArrToExpr (ps : Array MPoly) : MetaM Expr :=
  arrToExpr (mkConst ``MPoly) (ps.toList.map toExpr)

/-- Quote a `CellSide`. -/
def cellSideToExpr : CellSide → Expr
  | .exact => mkConst ``CellSide.exact
  | .lower => mkConst ``CellSide.lower
  | .upper => mkConst ``CellSide.upper

/-- Quote a `ResolutionAntecedent` (all three arms). -/
def antToExpr : ResolutionAntecedent → MetaM Expr
  | .clause cid => return mkApp (mkConst ``ResolutionAntecedent.clause) (toExpr cid)
  | .arith core proj => return (mkApp2 (mkConst ``ResolutionAntecedent.arith)
      (← litsArrToExpr core) (← litsArrToExpr proj))
  | .decision l => return (mkApp (mkConst ``ResolutionAntecedent.decision)
      (Refute.litToExpr l))

/-- Quote a `TraceStep` — all nine arms (DumpPP `:58-76` coverage,
Expr-side). The `thomQuadratic` arm reuses `Refute.thomStepToExpr`. -/
def stepToExpr : TraceStep → MetaM Expr
  | .leafNumeric x => return mkApp (mkConst ``TraceStep.leafNumeric) (toExpr x)
  | .linearRoot k y p mkNeg lcFact =>
    return (mkAppN (mkConst ``TraceStep.linearRoot)
      #[Refute.rootKindToExpr k, toExpr y, toExpr p, toExpr mkNeg, toExpr lcFact])
  | .thomQuadratic k y i p sq sa spd sp =>
    return Refute.thomStepToExpr k y i p sq sa spd sp
  | .rootGeneric k y i p =>
    return (mkAppN (mkConst ``TraceStep.rootGeneric)
      #[Refute.rootKindToExpr k, toExpr y, toExpr i, toExpr p])
  | .cellBound side k y i p =>
    return (mkAppN (mkConst ``TraceStep.cellBound)
      #[cellSideToExpr side, Refute.rootKindToExpr k, toExpr y, toExpr i, toExpr p])
  | .pseudoDivision f eq x d r lcSign isEven =>
    return (mkAppN (mkConst ``TraceStep.pseudoDivision)
      #[toExpr f, toExpr eq, toExpr x, toExpr d, toExpr r, toExpr lcSign,
        toExpr isEven])
  | .factorSplit p fs vanished =>
    return (mkAppN (mkConst ``TraceStep.factorSplit)
      #[toExpr p, ← mpolyArrToExpr fs, ← mpolyArrToExpr vanished])
  | .intBranch x lo =>
    return mkApp2 (mkConst ``TraceStep.intBranch) (toExpr x) (toExpr lo)
  | .resolution ant =>
    return (mkApp (mkConst ``TraceStep.resolution) (← antToExpr ant))

/-- Quote an `Array TraceStep`. -/
def stepsToExpr (steps : Array TraceStep) : MetaM Expr := do
  arrToExpr (mkConst ``TraceStep) (← steps.toList.mapM stepToExpr)

/-- Quote a `Clause` (structure-ctor application). -/
def clauseToExpr (c : Clause) : MetaM Expr := do
  return (mkApp3 (mkConst ``Clause.mk) (← litsArrToExpr c.lits)
    (toExpr c.learned) (toExpr c.deleted))

/-- Quote the clause table (`Array Clause`). -/
def clausesToExpr (clauses : Array Clause) : MetaM Expr := do
  arrToExpr (mkConst ``Clause) (← clauses.toList.mapM clauseToExpr)

/-- Quote a `TraceBundle` (structure-ctor application). -/
def bundleToExpr (b : TraceBundle) : MetaM Expr := do
  return (mkApp2 (mkConst ``TraceBundle.mk) (← stepsToExpr b.steps)
    (← litsArrToExpr b.lemma))

/-- Quote an `Option TraceBundle`. -/
def optBundleToExpr : Option TraceBundle → MetaM Expr
  | none => return mkApp (mkConst ``Option.none [levelZero]) (mkConst ``TraceBundle)
  | some b => return (mkApp2 (mkConst ``Option.some [levelZero])
      (mkConst ``TraceBundle) (← bundleToExpr b))

/-- Quote the bundle table (`Array (Option TraceBundle)`). -/
def bundlesToExpr (bundles : Array (Option TraceBundle)) : MetaM Expr := do
  arrToExpr (mkApp (mkConst ``Option [levelZero]) (mkConst ``TraceBundle))
    (← bundles.toList.mapM optBundleToExpr)

/-- Quote a refutation snapshot (the `s.refutation` payload,
`Walk.SnapshotTy`): nested `Prod.mk` over the four components. -/
def snapshotToExpr (snap : Array (Option Atom) × Array Clause ×
    Array (Option TraceBundle) × TraceBundle) : MetaM Expr := do
  let (atoms, clauses, bundles, fin) := snap
  mkAppM ``Prod.mk #[← atomsToExpr atoms,
    ← mkAppM ``Prod.mk #[← clausesToExpr clauses,
      ← mkAppM ``Prod.mk #[← bundlesToExpr bundles, ← bundleToExpr fin]]]

end LeanNonlinearArith.Nlsat.Quote
