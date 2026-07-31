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

/-! ## nla-12c.3 — propagation -/

private def gtA (p : MPoly) : IneqAtom := IneqAtom.mk .gt [(p, false)]
private def ltA (p : MPoly) : IneqAtom := IneqAtom.mk .lt [(p, false)]
private def xm (c : Int) : MPoly := MPoly.add x0 (MPoly.ofInt (-c))
private def x0sq1 : MPoly := MPoly.add (MPoly.mul x0 x0) (MPoly.ofInt 1)

private def initStage : SolverM Unit := do
  Solver.init
  let _ ← mkVar false
  newStage

/-- infeasible[x] is exactly the single interval (−∞, q] (closed). -/
private def checkUptoClosed (x : Var) (q : Rat) : SolverM Bool := do
  match (← get).infeasible[x]! with
  | some d =>
    if d.intervals.size != 1 then return false
    let iv := d.intervals[0]!
    if !iv.lowerInf || iv.upperInf || iv.upperOpen then return false
    return (← liftC (CellStore.read iv.upper)) == .rat q
  | none => return false

/-- infeasible[x] is exactly (q, ∞) (open). -/
private def checkAboveOpen (x : Var) (q : Rat) : SolverM Bool := do
  match (← get).infeasible[x]! with
  | some d =>
    if d.intervals.size != 1 then return false
    let iv := d.intervals[0]!
    if !iv.upperInf || iv.lowerInf || !iv.lowerOpen then return false
    return (← liftC (CellStore.read iv.lower)) == .rat q
  | none => return false

-- subset: boundary and sweep cases
#guard CellStore.run' (do
  let u01 ← IntervalSet.mk true true (.rat 0) false false (.rat 1) ⟨0, false⟩
  let u02 ← IntervalSet.mk true true (.rat 0) false false (.rat 2) ⟨0, false⟩
  let a ← IntervalSet.subset none u01
  let b ← IntervalSet.subset u01 none
  let c ← IntervalSet.subset u01 u02
  let d ← IntervalSet.subset u02 u01
  return a && !b && c && !d)

-- case (a): empty infeasible ⇒ propagate the literal (just: ~l only)
#guard Solver.run' (do
  initStage
  let l ← mkIneqLiteral (gtA x0sq1) -- x0²+1 > 0: always true
  let cid ← mkClause #[l] false
  let r ← processClauses #[cid]
  let s ← get
  return r == some none
    && s.bvalues[l.bvar]! == .true
    && s.justifications[l.bvar]! == .lazy #[l.negate] #[])

-- case (b): full infeasible ⇒ propagate ~l (just: l only); the clause
-- is then all-false ⇒ conflict (z3 returns false after the loop)
#guard Solver.run' (do
  initStage
  let l ← mkIneqLiteral (ltA x0sq1) -- x0²+1 < 0: never
  let cid ← mkClause #[l] false
  let r ← processClauses #[cid]
  let s ← get
  return r == some (some cid)
    && s.bvalues[l.bvar]! == .false
    && s.justifications[l.bvar]! == .lazy #[l] #[])

-- case (f): single undef ⇒ assign with clause justification +
-- updt_infeasible (trail-saved)
#guard Solver.run' (do
  initStage
  let l ← mkIneqLiteral (gtA (xm 1)) -- x0 > 1
  let cid ← mkClause #[l] false
  let r ← processClauses #[cid]
  let s ← get
  return r == some none
    && s.bvalues[l.bvar]! == .true
    && s.justifications[l.bvar]! == .clause cid
    && s.trail.contains (.infeasibleUpdt 0 none)
    && (← checkUptoClosed 0 1))

-- case (c): infeasible ⊆ current set ⇒ propagate with the current
-- set's justifications + ~l
#guard Solver.run' (do
  initStage
  let l1 ← mkIneqLiteral (gtA (xm 1)) -- x0 > 1 ⇒ xk_set = (−∞, 1]
  let cid1 ← mkClause #[l1] false
  let _ ← processClauses #[cid1]
  let l2 ← mkIneqLiteral (gtA x0) -- x0 > 0 ⇒ infeasible (−∞, 0] ⊆ xk_set
  let cid2 ← mkClause #[l2] false
  let r ← processClauses #[cid2]
  let s ← get
  return r == some none
    && s.bvalues[l2.bvar]! == .true
    && s.justifications[l2.bvar]! == .lazy #[l1, l2.negate] #[cid1])

-- case (d): union with current set = ℝ ⇒ propagate ~l justified by the
-- union WITHOUT ~l pushed (include_l = false); all-false afterwards ⇒
-- conflict (genuine: x0 ≤ 0 ∧ x0 ≥ 1 is UNSAT)
#guard Solver.run' (do
  initStage
  let g0 ← mkIneqLiteral (gtA x0)
  let l1 : Literal := ⟨g0.bvar, true⟩ -- x0 ≤ 0 ⇒ xk_set = (0, ∞)
  let cid1 ← mkClause #[l1] false
  let _ ← processClauses #[cid1]
  let lt1 ← mkIneqLiteral (ltA (xm 1))
  let l2 : Literal := ⟨lt1.bvar, true⟩ -- x0 ≥ 1 ⇒ infeasible (−∞, 1)
  let cid2 ← mkClause #[l2] false
  let r ← processClauses #[cid2]
  let s ← get
  return r == some (some cid2)
    && s.bvalues[lt1.bvar]! == .true -- propagated ¬l2 = x0 < 1
    && s.justifications[lt1.bvar]! == .lazy #[l2, l1] #[cid2, cid1])

-- case (e): all literals false ⇒ conflict, the clause id is returned
#guard Solver.run' (do
  initStage
  let g0 ← mkIneqLiteral (gtA x0)
  let cid1 ← mkClause #[⟨g0.bvar, true⟩] false -- x0 ≤ 0
  let _ ← processClauses #[cid1]
  let cid2 ← mkClause #[⟨g0.bvar, false⟩] false -- x0 > 0: false now
  let r ← processClauses #[cid2]
  return r == some (some cid2))

-- case (g): 2+ undef ⇒ decide the first (lit_lt order) + updt_infeasible
#guard Solver.run' (do
  initStage
  let l1 ← mkIneqLiteral (gtA x0)
  let l2 ← mkIneqLiteral (gtA (xm 1))
  let cid ← mkClause #[l2, l1] false -- sorted to #[l1, l2]
  let r ← processClauses #[cid]
  let s ← get
  return r == some none
    && s.decisions == 1 && s.scopeLvl == 1
    && s.bvalues[l1.bvar]! == .true
    && s.justifications[l1.bvar]! == .decision
    && (← checkUptoClosed 0 0))

-- case (h): lazy mode 2 skips learned clauses (not satisfied, no
-- action taken)
#guard Solver.run' (do
  initStage
  modify fun s => { s with lazyMode := 2 }
  let l ← mkIneqLiteral (gtA x0)
  let cid ← mkClause #[l] true -- learned
  let r ← processClauses #[cid]
  let s ← get
  return r == some none && s.bvalues[l.bvar]! == .undef)

-- boolean path: unit assign / decide / conflict
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  let cid ← mkClause #[⟨pb2, false⟩, ⟨pb1, false⟩] false
  let r ← processClauses #[cid]
  let s ← get
  -- both undef ⇒ decide the first by literal index (pb1)
  return r == some none && s.decisions == 1
    && s.bvalues[pb1]! == .true && s.justifications[pb1]! == .decision)

#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  assign ⟨pb1, true⟩ (.clause 0) -- pb1 = false
  let cid ← mkClause #[⟨pb1, false⟩, ⟨pb2, false⟩] false
  let r ← processClauses #[cid]
  let s ← get
  -- unit ⇒ assign pb2 true with the clause justification
  return r == some none && s.bvalues[pb2]! == .true
    && s.justifications[pb2]! == .clause cid)

#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  assign ⟨pb1, true⟩ (.clause 0)
  let cid ← mkClause #[⟨pb1, false⟩] false -- wants pb1 true: conflict
  let r ← processClauses #[cid]
  return r == some (some cid))

/-! ## nla-12c.4 — search, SAT mode (models verified by evaluation) -/

private def x0sq2 : MPoly := MPoly.add (MPoly.mul x0 x0) (MPoly.ofInt (-2))

/-- The board's SAT acceptance: every input clause has a true literal
under the produced assignment (z3's `check_satisfied(m_clauses)`
CASSERT made an external pin). -/
private def modelChecksOut (cids : Array Nat) : SolverM Bool := do
  for cid in cids do
    let c := (← get).clauses[cid]!
    if (← isSatisfiedClause c) != some true then return false
  return true

-- boolean-only SAT, with a negative-first decision
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  let c1 ← mkClause #[⟨pb1, false⟩, ⟨pb2, false⟩] false
  let r ← search stubResolve
  let s ← get
  return r == some .true
    && s.bvalues[pb1]! == .false -- negative-first decide
    && s.bvalues[pb2]! == .true  -- unit after the decide
    && (← modelChecksOut #[c1]))

-- one arith var: x0² − 2 > 0 ∧ x0 < 2
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let gt ← mkIneqLiteral (gtA x0sq2)
  let lt ← mkIneqLiteral (ltA (xm 2))
  let c1 ← mkClause #[gt] false
  let c2 ← mkClause #[lt] false
  let r ← search stubResolve
  let s ← get
  return r == some .true
    && s.assignment.contains 0
    && (← modelChecksOut #[c1, c2]))

-- two arith vars, conflict-free: x0 > 0 ∧ x1 > x0
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let _ ← mkVar false
  let g0 ← mkIneqLiteral (gtA x0)
  let g10 ← mkIneqLiteral (gtA (MPoly.sub x1 x0))
  let c1 ← mkClause #[g0] false
  let c2 ← mkClause #[g10] false
  let r ← search stubResolve
  let s ← get
  return r == some .true
    && s.assignment.contains 0 && s.assignment.contains 1
    && (← modelChecksOut #[c1, c2]))

-- EQ atom with irrational witness (shared-endpoint pick): x0² − 2 = 0
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let eq ← mkIneqLiteral (IneqAtom.mk .eq [(x0sq2, false)])
  let c1 ← mkClause #[eq] false
  let r ← search stubResolve
  let s ← get
  return r == some .true
    && (← modelChecksOut #[c1]))

-- UNSAT at propagation level, no resolve: the abort image (stub
-- resolve returns none on the genuine conflict x0 ≤ 0 ∧ x0 ≥ 1)
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let g0 ← mkIneqLiteral (gtA x0)
  let lt1 ← mkIneqLiteral (ltA (xm 1))
  let c1 ← mkClause #[⟨g0.bvar, true⟩] false -- x0 ≤ 0
  let c2 ← mkClause #[⟨lt1.bvar, true⟩] false -- x0 ≥ 1
  let r ← search stubResolve
  return r == none)

-- init_search unwinds everything
#guard Solver.run' (do
  Solver.init
  let pb ← mkBoolVar
  let _ ← mkVar false
  decide ⟨pb, false⟩
  newStage
  let c ← liftC (CellStore.fresh (.rat 3))
  modify fun s => { s with assignment := s.assignment.set 0 c }
  initSearch
  let s ← get
  return s.scopeLvl == 0 && s.xk == none && s.trail.isEmpty
    && s.assignment.isEmpty
    && s.bvalues.all (· == .undef))

/-! ## nla-12c.5 — resolve (mock explain: faithful for boolean and
stage-0 conflicts, which have no lower variables to project) -/

-- trivial boolean UNSAT
#guard Solver.run' (do
  Solver.init
  let pb ← mkBoolVar
  let _ ← mkClause #[⟨pb, false⟩] false
  let _ ← mkClause #[⟨pb, true⟩] false
  let r ← search (resolve mockExplain)
  let s ← get
  return r == some .false && s.conflicts == 1)

-- chained resolution: decision reversal via a learned unit, then the
-- empty lemma at level 0 (2 conflicts)
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  let _ ← mkClause #[⟨pb1, false⟩, ⟨pb2, false⟩] false
  let _ ← mkClause #[⟨pb1, true⟩, ⟨pb2, false⟩] false
  let _ ← mkClause #[⟨pb2, true⟩] false
  let r ← search (resolve mockExplain)
  let s ← get
  return r == some .false
    && s.conflicts ≥ 2
    && s.clauses.any (fun c => c.learned && c.lits == #[⟨pb1, false⟩]))

-- stage-0 arith UNSAT: x0 ≤ 0 ∧ x0 ≥ 1 (mock explain is faithful —
-- there is nothing below stage 0 to project)
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let g0 ← mkIneqLiteral (gtA x0)
  let lt1 ← mkIneqLiteral (ltA (xm 1))
  let _ ← mkClause #[⟨g0.bvar, true⟩] false -- x0 ≤ 0
  let _ ← mkClause #[⟨lt1.bvar, true⟩] false -- x0 ≥ 1
  let r ← search (resolve mockExplain)
  return r == some .false)

-- mixed: case-1 STAGE backjump with a learned clause, then reprocess
-- (z3's `goto start`): [b1 ∨ x0 > 0] ∧ [¬b1] ∧ [x0 < −1]
#guard Solver.run' (do
  Solver.init
  let _ ← mkVar false
  let pb ← mkBoolVar
  let g0 ← mkIneqLiteral (gtA x0)
  let lt1 ← mkIneqLiteral (ltA (xm (-1)))
  let _ ← mkClause #[⟨pb, false⟩, g0] false
  let _ ← mkClause #[⟨pb, true⟩] false
  let _ ← mkClause #[lt1] false
  let r ← search (resolve mockExplain)
  let s ← get
  return r == some .false
    && s.clauses.any (fun c => c.learned && c.lits == #[⟨pb, false⟩]))

-- case-2 backjump: the learned clause reverses a decision, then SAT
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  let pb3 ← mkBoolVar
  let c1 ← mkClause #[⟨pb1, false⟩, ⟨pb2, false⟩, ⟨pb3, false⟩] false
  let c2 ← mkClause #[⟨pb3, true⟩, ⟨pb2, false⟩] false
  let r ← search (resolve mockExplain)
  let s ← get
  return r == some .true
    && s.bvalues[pb2]! == .true -- reversed from the negative-first decide
    && s.clauses.any (fun c => c.learned
      && c.lits == #[⟨pb1, false⟩, ⟨pb2, false⟩])
    && (← modelChecksOut #[c1, c2]))

-- max_conflicts gate
#guard Solver.run' (do
  Solver.init
  let pb1 ← mkBoolVar
  let pb2 ← mkBoolVar
  let _ ← mkClause #[⟨pb1, false⟩, ⟨pb2, false⟩] false
  let _ ← mkClause #[⟨pb1, true⟩, ⟨pb2, false⟩] false
  let _ ← mkClause #[⟨pb2, true⟩] false
  modify fun s => { s with maxConflicts := 1 }
  let r ← search (resolve mockExplain)
  return r == some .undef)

end LeanNonlinearArith.Nlsat.Tests
