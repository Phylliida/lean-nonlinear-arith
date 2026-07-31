import LeanNonlinearArith.Nlsat.Solver

/-!
# nla-12c.1 tests — solver scaffold pins

Construction, atom hash-consing, the max_var/degree family (incl. the
null-poisoning of `max_var(sz, cls)`), the `lit_lt` order, and clause
sort + watch attachment. Store discipline: one `SolverM` computation
per scenario (`Solver.run'`).
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Solver

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def x2 : MPoly := MPoly.ofVar 2

/-! ## init / registration -/

-- mk_true_bvar: bvar 0, undef value, unit input clause, watched on
-- bwatches[0] (no arith literal ⇒ max_bvar = 0)
#guard Solver.run' (do
  Solver.init
  let s ← get
  return s.atoms.size == 1 && s.atoms[0]! == none
    && s.bvalues[0]! == .undef
    && s.clauses.size == 1 && !s.clauses[0]!.learned
    && s.clauses[0]!.lits == #[⟨0, false⟩]
    && s.bwatches[0]! == #[0])

-- mk_var registration: ids, flags, identity perms, empty per-var state
#guard Solver.run' (do
  Solver.init
  let a ← mkVar true
  let b ← mkVar false
  let s ← get
  return a == 0 && b == 1
    && s.isInt == #[true, false]
    && s.watches.size == 2 && s.infeasible.size == 2
    && s.perm == #[0, 1] && s.invPerm == #[0, 1]
    && s.var2eq == #[none, none])

/-! ## atom hash-consing (z3 ineq_atom_table / root_atom_table) -/

#guard Solver.run' (do
  Solver.init
  let a1 := IneqAtom.mk .gt [(x0, false)]
  let b1 ← mkIneqAtom a1
  let b2 ← mkIneqAtom a1
  let b3 ← mkIneqAtom (IneqAtom.mk .lt [(x0, false)])
  return b1 == 1 && b2 == 1 && b3 == 2)

#guard Solver.run' (do
  Solver.init
  let r1 ← mkRootAtom (RootAtom.mk .eq 0 1 x1)
  let r2 ← mkRootAtom (RootAtom.mk .eq 0 1 x1)
  let r3 ← mkRootAtom (RootAtom.mk .lt 0 1 x1)
  return r1 == 1 && r2 == 1 && r3 == 2)

/-! ## max_var / degree family -/

-- max_var(sz, cls): ordinary max, null-poisoning (constant atom's
-- max_var is z3's UINT_MAX ⇒ greatest), and last-assignment-wins
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let _ ← mkVar false
  let arith ← mkIneqLiteral (IneqAtom.mk .gt [(x1, false)])            -- maxVar 1
  let constA ← mkIneqLiteral (IneqAtom.mk .gt [(MPoly.ofInt 5, false)]) -- maxVar none
  let s ← get
  return maxVarLits s #[arith] == some 1
    && maxVarLits s #[arith, constA] == none
    && maxVarLits s #[arith, constA, arith] == some 1
    && maxVarLits s #[⟨0, false⟩] == none)

-- degree(atom): max factor degree in the atom's max_var; constant ⇒ 0
#guard
  let sqA := Atom.ineq (IneqAtom.mk .gt [(MPoly.mul x0 x0, false)])
  let linA := Atom.ineq (IneqAtom.mk .gt [(x0, false)])
  let constA := Atom.ineq (IneqAtom.mk .gt [(MPoly.ofInt 5, false)])
  Solver.degreeAtom sqA == 2 && Solver.degreeAtom linA == 1
    && Solver.degreeAtom constA == 0

/-! ## lit_lt -/

#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let _ ← mkVar false
  let pb ← mkBoolVar                                                  -- bvar 1, pure
  let d0 ← mkIneqLiteral (IneqAtom.mk .gt [(x0, false)])              -- mv 0, deg 1
  let d1 ← mkIneqLiteral (IneqAtom.mk .gt [(x1, false)])              -- mv 1, deg 1
  let sq0 ← mkIneqLiteral (IneqAtom.mk .gt [(MPoly.mul x0 x0, false)]) -- mv 0, deg 2
  let eq0 ← mkIneqLiteral (IneqAtom.mk .eq [(x0, false)])             -- mv 0, deg 1, eq
  let cn ← mkIneqLiteral (IneqAtom.mk .gt [(MPoly.ofInt 5, false)])   -- mv none
  let s ← get
  -- pure-boolean literals first; then max_var ascending; null max_var
  -- (z3 UINT_MAX) sorts LAST among arith; degree tiebreak on same
  -- max_var; non-eq before eq on ties; literal index last
  return litLt s ⟨pb, false⟩ d0 && !litLt s d0 ⟨pb, false⟩
    && litLt s d0 d1 && !litLt s d1 d0
    && litLt s d1 cn && litLt s d0 cn && !litLt s cn d0
    && litLt s d0 sq0 && !litLt s sq0 d0
    && litLt s d0 eq0 && !litLt s eq0 d0
    && litLt s ⟨d0.bvar, false⟩ ⟨d0.bvar, true⟩
    && !litLt s ⟨d0.bvar, true⟩ ⟨d0.bvar, false⟩)

/-! ## mk_clause: lit_lt sort + watch attachment -/

-- arith clause: sorted (pure-bool first, then max_var), watched on
-- the clause max_var
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let _ ← mkVar false
  let _ ← mkVar false
  let d2 ← mkIneqLiteral (IneqAtom.mk .gt [(x2, false)])
  let d0 ← mkIneqLiteral (IneqAtom.mk .gt [(x0, false)])
  let pb ← mkBoolVar
  let cid ← mkClause #[d2, ⟨pb, false⟩, d0] false
  let s ← get
  return s.clauses[cid]!.lits == #[⟨pb, false⟩, d0, d2]
    && s.watches[2]!.contains cid
    && !(s.watches[0]!.contains cid))

-- pure-boolean clause: watched on max_bvar, sorted by literal index
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  let cid ← mkClause #[⟨pb2, true⟩, ⟨pb1, false⟩] false
  let s ← get
  return s.bwatches[max pb1 pb2]!.contains cid
    && s.clauses[cid]!.lits == #[⟨pb1, false⟩, ⟨pb2, true⟩])

-- learned clauses append to the same table with the flag set
#guard Solver.run' (do
  Solver.init
  let pb ← mkBoolVar
  let cid ← mkClause #[⟨pb, false⟩] true
  let s ← get
  return s.clauses[cid]!.learned && s.clauses.size == 2)

/-- Test helper: bind x to a rational value in the assignment store. -/
private def assignVal (x : Var) (q : Rat) : SolverM Unit := do
  let c ← liftC (CellStore.fresh (.rat q))
  modify fun s => { s with assignment := s.assignment.set x c }

/-! ## assign / decide / stages / levels -/

#guard Solver.run' (do
  Solver.init
  let pb ← mkBoolVar
  let sz0 := (← get).trail.size
  decide ⟨pb, false⟩
  let s ← get
  return s.scopeLvl == 1 && s.decisions == 1 && s.propagations == 0
    && s.bvalues[pb]! == .true && s.levels[pb]! == 1
    && s.justifications[pb]! == .decision
    && s.trail.size == sz0 + 2
    && s.trail[sz0]! == .newLevel
    && s.trail[sz0 + 1]! == .bvarAssignment pb)

-- assign with a clause justification: propagation counter, sign flip
#guard Solver.run' (do
  Solver.init
  let pb ← mkBoolVar
  assign ⟨pb, true⟩ (.clause 0)
  let s ← get
  return s.bvalues[pb]! == .false && s.propagations == 1
    && assignedValue s ⟨pb, true⟩ == .true
    && assignedValue s ⟨pb, false⟩ == .false)

-- new_stage: first from null, then increment (init's mk_clause pushes
-- no trail entry, so the trail is exactly the two stage markers)
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let _ ← mkVar false
  newStage
  newStage
  let s ← get
  return s.xk == some 1 && s.stages == 2
    && s.trail == #[.newStage, .newStage])

/-! ## value -/

#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let gt ← mkIneqLiteral (IneqAtom.mk .gt [(x0, false)])
  let lt ← mkIneqLiteral (IneqAtom.mk .lt [(x0, false)])
  -- unassigned + max_var unassigned ⇒ undef
  let v0 ← value gt
  -- assigned literal short-circuits
  assign gt (.clause 0)
  let v1 ← value gt
  let v1n ← value ⟨gt.bvar, true⟩
  -- evaluator path: x0 ↦ 1 makes x0 > 0 true and x0 < 0 false
  assignVal 0 1
  undoUntilUnassigned gt.bvar
  let v2 ← value gt
  let v3 ← value lt
  return v0 == some .undef
    && v1 == some .true && v1n == some .false
    && v2 == some .true && v3 == some .false)

-- is_satisfied / is_inconsistent on clauses
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let gt ← mkIneqLiteral (IneqAtom.mk .gt [(x0, false)])
  let lt ← mkIneqLiteral (IneqAtom.mk .lt [(x0, false)])
  let cid ← mkClause #[gt, lt] false
  let c := (← get).clauses[cid]!
  let s0 ← isSatisfiedClause c   -- both undef ⇒ not satisfied
  assignVal 0 1
  let s1 ← isSatisfiedClause c   -- gt true
  let i1 ← isInconsistent c.lits -- lt false but gt true ⇒ no
  assignVal 0 0
  -- x0 ↦ 0: gt false, lt false ⇒ inconsistent
  return s0 == some false && s1 == some true && i1 == some false
    && (← isInconsistent c.lits) == some true)

/-! ## undo -/

-- undo_bvar_assignment: undef + bk rewind for pure booleans only
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  modify fun s => { s with bk := some pb2 }
  assign ⟨pb1, false⟩ .decision
  let sz := (← get).trail.size
  undoUntilSize (sz - 1)
  let s ← get
  return s.bvalues[pb1]! == .undef && s.bk == some pb1)

-- arith literal: no bk rewind
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let arith ← mkIneqLiteral (IneqAtom.mk .gt [(x0, false)])
  modify fun s => { s with bk := some 0 }
  assign arith .decision
  let sz := (← get).trail.size
  undoUntilSize (sz - 1)
  return (← get).bk == some 0)

-- undo_new_stage quirk: decrements, then resets the var it RETURNS
-- to; the exited stage keeps its assignment; x0 case nulls out
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let _ ← mkVar false
  let _ ← mkVar false
  assignVal 0 10
  assignVal 1 11
  assignVal 2 12
  newStage
  newStage
  newStage
  undoUntilStage (some 1)
  let s ← get
  return s.xk == some 1
    && s.assignment.contains 0    -- untouched
    && !s.assignment.contains 1   -- reset (the var returned to)
    && s.assignment.contains 2)   -- z3 quirk: exited stage stays!

-- full unwind to the boolean phase
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  newStage
  undoUntilStage none
  return (← get).xk == none)

-- undo_until_level: pops assignments and levels back to the target
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  newLevel
  assign ⟨pb1, false⟩ .decision
  newLevel
  assign ⟨pb2, false⟩ .decision
  undoUntilLevel 1
  let s ← get
  return s.scopeLvl == 1 && s.bvalues[pb2]! == .undef
    && s.bvalues[pb1]! == .true)

/-! ## updt_eq -/

private def eqAtom (p : MPoly) : IneqAtom := IneqAtom.mk .eq [(p, false)]

-- var2eq tracks the smallest-degree asserted equality; trail restores
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  newStage
  let sq ← mkIneqLiteral (eqAtom (MPoly.mul x0 x0))   -- deg 2
  let lin ← mkIneqLiteral (eqAtom x0)                 -- deg 1
  let cb ← mkIneqLiteral (eqAtom (MPoly.mul (MPoly.mul x0 x0) x0)) -- deg 3
  assign sq .decision
  let v1 := (← get).var2eq[0]!
  assign lin (.clause 0)
  let v2 := (← get).var2eq[0]!
  assign cb (.clause 0)
  let v3 := (← get).var2eq[0]!
  -- undo the lin update: restores sq
  let sz := (← get).trail.size
  undoUntilSize (sz - 2)
  let v4 := (← get).var2eq[0]!
  return v1 == some sq.bvar && v2 == some lin.bvar && v3 == some lin.bvar
    && v4 == some sq.bvar)

-- gates: simplify_cores off / non-true value / non-EQ / multi-factor /
-- even factor / lazy with literals
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  newStage
  -- simplifyCores off
  modify fun s => { s with simplifyCores := false }
  let a ← mkIneqLiteral (eqAtom x0)
  assign a .decision
  let r1 := (← get).var2eq[0]!
  modify fun s => { s with simplifyCores := true }
  -- non-EQ atom
  let gt ← mkIneqLiteral (IneqAtom.mk .gt [(x0, false)])
  assign gt .decision
  let r2 := (← get).var2eq[0]!
  -- multi-factor EQ
  let mf ← mkIneqLiteral (IneqAtom.mk .eq [(x0, false), (x0, false)])
  assign mf .decision
  let r3 := (← get).var2eq[0]!
  -- even factor
  let ev ← mkIneqLiteral (IneqAtom.mk .eq [(x0, true)])
  assign ev .decision
  let r4 := (← get).var2eq[0]!
  -- lazy justification carrying literals
  let b ← mkIneqLiteral (eqAtom x0)
  assign b (.lazy #[⟨0, false⟩] #[])
  let r5 := (← get).var2eq[0]!
  return r1 == none && r2 == none && r3 == none && r4 == none
    && r5 == none)

-- lazy with EMPTY payloads proceeds (z3 gate: only nonempty skips)
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  newStage
  let a ← mkIneqLiteral (eqAtom x0)
  assign a (.lazy #[] #[])
  return (← get).var2eq[0]! == some a.bvar)

end LeanNonlinearArith.Nlsat.Tests
