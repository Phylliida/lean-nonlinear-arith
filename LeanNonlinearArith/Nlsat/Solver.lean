import LeanNonlinearArith.Nlsat.IntervalSet
import LeanNonlinearArith.Nlsat.Evaluator
import LeanNonlinearArith.Nlsat.EvaluatorTable

/-!
# nla-12c — the solver loop (z3 `nlsat_solver.cpp` @ **4.12.5**)

Faithful port of the 4.12.5 classic search (the parity target; the
working-tree checkout is 4.16-nightly and differs materially — nla-32).
Source text: `git show z3-4.12.5:src/nlsat/nlsat_solver.cpp`.

## Representation choices (behavior-faithful, not divergences)

* z3's `null_var`/`null_bool_var` (UINT_MAX) are `Option` here. Where
  z3's arithmetic on UINT_MAX is load-bearing (a constant atom's null
  max_var is the GREATEST in comparisons), that is replicated
  explicitly (`maxVarLits`, `optVarLt`) — including the null-poisoning
  behavior, per rule 3.
* z3's clause pointers are indices into ONE append-only table
  (`clauses`, with the `learned` flag inside); z3's `m_clauses` /
  `m_learned` iterations become filters. `del_clause` is unreachable
  under the nra entry (reorder fires pre-search when learned is empty)
  so ids are stable.
* Assumption tracking (`m_asm`, `m_lemma_assumptions`) is a declared
  non-port: the nra entry calls `check()` with no assumptions, so the
  layer is dead bookkeeping (BOARD nla-12c dead-code register).
* `checkpoint()` (rlimit cancel) is a no-op here; budgets land at
  nla-14 (`withLayerHeartbeats` directive).

## State

`solver::imp`'s fields map onto `Solver`; the cell store rides along
as `store` with `liftC` lifting `CellM` ops (store-era discipline:
`modify`-style updates, one `SolverM` computation per test scenario).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-! ## `lbool` -/

inductive LBool | false | undef | true
deriving Repr, DecidableEq, Inhabited

namespace LBool

/-- z3 `operator~(lbool)`. -/
def neg : LBool → LBool
  | .false => .true
  | .undef => .undef
  | .true => .false

/-- z3 `to_lbool`. -/
def ofBool (b : Bool) : LBool := if b then .true else .false

end LBool

/-! ## Justifications (`nlsat_justification.h` @ 4.12.5) -/

/-- `justification`: null / decision / clause / lazy. The lazy shape
carries the core literals plus justified clause ids (z3 stores literal
+ clause-pointer arrays inline; ids here). -/
inductive Justification
  | null
  | decision
  | clause (cid : Nat)
  | lazy (lits : Array Literal) (clauseIds : Array Nat)
deriving Repr, BEq, Inhabited

/-! ## Trail (`imp::trail` @ 4.12.5) -/

/-- The five trail kinds. z3's `INFEASIBLE_UPDT`/`UPDT_EQ` restore into
`m_xk` at undo time; the var is carried here explicitly (same program
points, no reliance on undo-time stage). -/
inductive TrailEntry
  | bvarAssignment (b : Nat)
  | infeasibleUpdt (x : Var) (oldSet : IntervalSet)
  | newLevel
  | newStage
  | updtEq (x : Var) (oldEq : Option Nat)
deriving Repr, BEq, Inhabited

/-! ## The solver state (`imp` @ 4.12.5) -/

structure Solver where
  store : CellStore := #[]
  assignment : Assignment := #[]
  atoms : Array (Option Atom) := #[]
  bvalues : Array LBool := #[]
  levels : Array Nat := #[]
  justifications : Array Justification := #[]
  bwatches : Array (Array Nat) := #[]
  dead : Array Bool := #[]
  isInt : Array Bool := #[]
  watches : Array (Array Nat) := #[]
  infeasible : Array IntervalSet := #[]
  var2eq : Array (Option Nat) := #[]
  perm : Array Var := #[]
  invPerm : Array Var := #[]
  clauses : Array Clause := #[]
  trail : Array TrailEntry := #[]
  bk : Option Nat := none
  xk : Option Var := none
  scopeLvl : Nat := 0
  stages : Nat := 0
  conflicts : Nat := 0
  propagations : Nat := 0
  decisions : Nat := 0
  maxConflicts : Nat := 4294967295 -- UINT_MAX (nlsat_params default)
  lazyMode : Nat := 0              -- `lazy` param default 0
  simplifyCores : Bool := true     -- `simplify_conflicts` default true
  fullDimensional : Bool := false  -- set by `check()` for 12d's explain
deriving Inhabited

abbrev SolverM := StateM Solver

/-- Lift a cell-store computation, threading the store in/out. -/
def liftC (f : CellM α) : SolverM α := fun s =>
  let (a, store') := f.run s.store
  (a, { s with store := store' })

/-- The empty solver state (declared field defaults honored). -/
def Solver.empty : Solver := {}

/-- Run a solver computation from the empty state (test ergonomics,
`CellStore.run'` analogue). Uses `Solver.empty` (NOT `default` — the
derived `Inhabited` ignores declared field defaults like
`simplifyCores := true`). -/
def Solver.run' (f : SolverM α) : α := (f.run Solver.empty).1

namespace Solver

/-! ## Boolean variable / variable registration -/

/-- z3 `mk_bool_var_core`: fresh bvar with undef value, null atom,
empty watches. (z3's `m_levels` default UINT_MAX is never observed —
levels are read only for assigned literals.) -/
def mkBoolVar : SolverM Nat := do
  let b := (← get).atoms.size
  modify fun s => { s with
    atoms := s.atoms.push none
    bvalues := s.bvalues.push .undef
    levels := s.levels.push 0
    justifications := s.justifications.push .null
    bwatches := s.bwatches.push #[]
    dead := s.dead.push false }
  return b

/-- z3 `mk_var` + `register_var`: fresh var with identity perm entries
and empty per-var state. -/
def mkVar (isInt : Bool) : SolverM Var := do
  let x := (← get).isInt.size
  modify fun s => { s with
    isInt := s.isInt.push isInt
    watches := s.watches.push #[]
    infeasible := s.infeasible.push none
    var2eq := s.var2eq.push none
    perm := s.perm.push x
    invPerm := s.invPerm.push x }
  return x

/-! ## Atoms (`mk_ineq_atom`/`mk_root_atom` @ 4.12.5)

z3 hash-conses atoms (`ineq_atom_table`/`root_atom_table`): the same
(kind, factors) or (kind, x, i, p) returns the SAME bool_var. Ported
as a structural-equality scan — creation is frontend-driven, not hot;
a map is future perf work, not fidelity work. -/

def mkIneqAtom (a : IneqAtom) : SolverM Nat := do
  let target := some (Atom.ineq a)
  match (← get).atoms.findIdx? (· == target) with
  | some b => return b
  | none =>
    let b ← mkBoolVar
    modify fun s => { s with atoms := s.atoms.set! b (some (Atom.ineq a)) }
    return b

def mkRootAtom (a : RootAtom) : SolverM Nat := do
  let target := some (Atom.root a)
  match (← get).atoms.findIdx? (· == target) with
  | some b => return b
  | none =>
    let b ← mkBoolVar
    modify fun s => { s with atoms := s.atoms.set! b (some (Atom.root a)) }
    return b

/-- z3 `mk_ineq_literal`: the positive literal on the (deduped) atom. -/
def mkIneqLiteral (a : IneqAtom) : SolverM Literal := do
  return ⟨← mkIneqAtom a, false⟩

/-- z3 `is_arith_atom` / `is_arith_literal`. -/
def isArithAtom (s : Solver) (b : Nat) : Bool :=
  match s.atoms[b]? with
  | some (some _) => true
  | _ => false

def isArithLiteral (s : Solver) (l : Literal) : Bool := isArithAtom s l.bvar

/-! ## max_var / max_bvar / degree (`:373`–`:462` @ 4.12.5) -/

/-- z3 `max_var(bool_var)`: the atom's max_var, none (null_var) for
pure booleans. -/
def maxVarB (s : Solver) (b : Nat) : Option Var :=
  match s.atoms[b]? with
  | some (some a) => a.maxVar
  | _ => none

/-- z3 `max_var(sz, cls)`: max over ARITH literals' atom max_vars.
z3's null_var is UINT_MAX — the GREATEST — so a constant atom (null
max_var) poisons the result back to null, and the last assignment
wins; the `none`-as-null fold below reproduces both exactly. -/
def maxVarLits (s : Solver) (lits : Array Literal) : Option Var := Id.run do
  let mut x : Option Var := none
  for l in lits do
    match s.atoms[l.bvar]? with
    | some (some a) =>
      let y := a.maxVar
      match x, y with
      | none, _ => x := y
      | some _, none => x := none
      | some xv, some yv => x := some (max xv yv)
    | _ => pure ()
  return x

/-- z3 `max_var(clause)`. -/
def maxVarClause (s : Solver) (c : Clause) : Option Var :=
  maxVarLits s c.lits

/-- z3 `max_bvar`: greatest bool_var index over all literals. -/
def maxBvar (c : Clause) : Nat :=
  c.lits.foldl (fun acc l => max acc l.bvar) 0

/-- z3 `degree(atom)`: ineq = max over factors of the degree in the
atom's max_var (constant atom ⇒ 0, as `pm.degree(p, null_var)`). -/
def degreeAtom (a : Atom) : Nat :=
  match a.maxVar with
  | none => 0
  | some v =>
    match a with
    | .ineq ia => ia.factors.foldl (fun acc (p, _) => max acc (p.degreeIn v)) 0
    | .root ra => ra.p.degreeIn v

/-- z3 `degree(clause)`: 0 for null max_var, else max atom degree. -/
def degreeClause (s : Solver) (c : Clause) : Nat := Id.run do
  match maxVarClause s c with
  | none => return 0
  | some _ =>
    let mut mx := 0
    for l in c.lits do
      match s.atoms[l.bvar]? with
      | some (some a) => mx := max mx (degreeAtom a)
      | _ => pure ()
    return mx

/-! ## `lit_lt` (`:757` @ 4.12.5) — the mk_clause sort

Pure-boolean literals first, then atom max_var ascending (null_var =
UINT_MAX sorts LAST), then atom degree ascending, then non-eq before
eq, then literal index. Semantic: fixes the clause literal order,
which fixes `first_undef` selection in process_*_clause. -/

/-- Option-var `<` with `none` (z3 null_var = UINT_MAX) as GREATEST. -/
def optVarLt : Option Var → Option Var → Bool
  | some a, some b => a < b
  | some _, none => true
  | _, _ => false

/-- z3 `atom::is_eq` (EQ or ROOT_EQ). -/
def atomIsEq : Atom → Bool
  | .ineq a => a.kind == .eq
  | .root a => a.kind == .eq

def litLt (s : Solver) (l1 l2 : Literal) : Bool :=
  match s.atoms[l1.bvar]?, s.atoms[l2.bvar]? with
  | some none, some none => l1.index < l2.index
  | some none, _ => true
  | _, some none => false
  | some (some a1), some (some a2) =>
    let x1 := a1.maxVar
    let x2 := a2.maxVar
    if optVarLt x1 x2 then true
    else if optVarLt x2 x1 then false
    else
      let d1 := degreeAtom a1
      let d2 := degreeAtom a2
      if d1 < d2 then true
      else if d1 > d2 then false
      else if !atomIsEq a1 && atomIsEq a2 then true
      else if atomIsEq a1 && !atomIsEq a2 then false
      else l1.index < l2.index
  | _, _ => l1.index < l2.index -- out-of-range: z3 SASSERT site, unreachable

/-! ## Clauses (`mk_clause`, `attach_clause` @ 4.12.5) -/

/-- z3 `attach_clause`: watch on the clause's max_var, or on its
max_bvar when it has no arith literal. -/
def attachClause (cid : Nat) : SolverM Unit := do
  let s ← get
  let c := s.clauses[cid]!
  match maxVarClause s c with
  | some x =>
    modify fun s => { s with watches := s.watches.modify x (·.push cid) }
  | none =>
    let b := maxBvar c
    modify fun s => { s with bwatches := s.bwatches.modify b (·.push cid) }

/-- z3 `mk_clause(num, lits, learned, a)`: fresh id, `lit_lt` sort,
append to the table, attach to watches. (z3's assumption argument is
always null under the nra entry — declared non-port.) -/
def mkClause (lits : Array Literal) (learned : Bool) : SolverM Nat := do
  let cid := (← get).clauses.size
  let sorted := lits.qsort (litLt (← get))
  modify fun s => { s with clauses := s.clauses.push ⟨sorted, learned⟩ }
  attachClause cid
  return cid

/-- z3 `mk_true_bvar`: bvar 0 is the true constant, asserted by a unit
input clause. -/
def mkTrueBvar : SolverM Unit := do
  let b ← mkBoolVar
  let _ ← mkClause #[⟨b, false⟩] false

/-- z3's imp-ctor initialization (post `updt_params`). -/
def init : SolverM Unit := mkTrueBvar

/-! ## nla-12c.2 — assignment, stages/levels, trail + undo, value -/

/-- z3 `assigned_value`: the search-engine value (sign-flipped). -/
def assignedValue (s : Solver) (l : Literal) : LBool :=
  let bv := s.bvalues[l.bvar]!
  if l.neg then bv.neg else bv

/-- z3 `updt_eq` (`:1280`): maintain `m_var2eq[x]` = smallest-degree
asserted single-factor odd equality on x (z3 stores the atom; the bvar
is stored here — atoms are stable). Assumption gates are always-null
under the nra entry (declared non-port). -/
def updtEq (b : Nat) (j : Justification) : SolverM Unit := do
  let s ← get
  if !s.simplifyCores then return
  if s.bvalues[b]! != .true then return
  match s.atoms[b]? with
  | some (some (.ineq a)) =>
    if a.kind != .eq || a.factors.length > 1
        || (a.factors.head?.map (·.2)).getD false then return
    match j with
    | .lazy lits cids => if !lits.isEmpty || !cids.isEmpty then return
    | _ => pure ()
    match s.xk with
    | none => pure () -- z3 SASSERT(x != null_var): unreachable by construction
    | some x =>
      match s.var2eq[x]! with
      | some oldB =>
        let oldDeg :=
          match s.atoms[oldB]! with
          | some oldA => degreeAtom oldA
          | none => 0 -- unreachable: var2eq only holds eq-atom bvars
        if oldDeg ≤ degreeAtom (.ineq a) then return
      | none => pure ()
      modify fun s => { s with
        trail := s.trail.push (.updtEq x s.var2eq[x]!)
        var2eq := s.var2eq.set! x (some b) }
  | _ => return

/-- z3 `assign` (`:1136`): set value/level/justification, trail, count,
then `updt_eq`. SASSERTs (undef target, non-null justification) are
construction preconditions of the call sites. -/
def assign (l : Literal) (j : Justification) : SolverM Unit := do
  match j with
  | .decision => modify fun s => { s with decisions := s.decisions + 1 }
  | _ => modify fun s => { s with propagations := s.propagations + 1 }
  let b := l.bvar
  modify fun s => { s with
    bvalues := s.bvalues.set! b (LBool.ofBool !l.neg)
    levels := s.levels.set! b s.scopeLvl
    justifications := s.justifications.set! b j
    trail := s.trail.push (.bvarAssignment b) }
  updtEq b j

/-- z3 `new_level` (`:1115`). `m_evaluator.push()` is a no-op at
4.12.5 (verified) — nothing to port there. -/
def newLevel : SolverM Unit := do
  modify fun s => { s with
    scopeLvl := s.scopeLvl + 1
    trail := s.trail.push .newLevel }

/-- z3 `decide` (`:1160`). -/
def decide (l : Literal) : SolverM Unit := do
  newLevel
  assign l .decision

/-- z3 `new_stage` (`:1442`). -/
def newStage : SolverM Unit := do
  modify fun s => { s with
    stages := s.stages + 1
    trail := s.trail.push .newStage
    xk := match s.xk with
      | none => some 0
      | some x => some (x + 1) }

/-! ### trail save helpers (12c.3 saves from `updt_infeasible`/`updt_eq`;
exposed for tests) -/

def saveSetUpdtTrail (x : Var) (oldSet : IntervalSet) : SolverM Unit :=
  modify fun s => { s with trail := s.trail.push (.infeasibleUpdt x oldSet) }

/-! ### undo (`:986`–`:1108` @ 4.12.5) -/

/-- z3 `undo_bvar_assignment`: undef the var and REWIND `m_bk` for pure
booleans (`b < m_bk ⇒ m_bk = b`; z3's null bk is UINT_MAX ⇒ always
rewinds, matched by the `none` branch). -/
def undoBvarAssignment (b : Nat) : SolverM Unit := do
  modify fun s => { s with
    bvalues := s.bvalues.set! b .undef
    levels := s.levels.set! b 0
    justifications := s.justifications.set! b .null
    bk := if !isArithAtom s b
        then match s.bk with
          | none => some b
          | some cur => if b < cur then some b else s.bk
        else s.bk }

/-- z3 `undo_set_updt`: restore the infeasible set. z3 restores into
the undo-TIME `m_xk`; infeasible updates always pop inside their own
stage's trail segment (they are saved only by `updt_infeasible`, which
requires `m_xk != null`, and their stage marker pops after them), so
the saved var and the undo-time var coincide — the saved var is used
directly. z3's null/size guards are construction-excluded. -/
def undoSetUpdt (x : Var) (oldSet : IntervalSet) : SolverM Unit := do
  modify fun s => { s with infeasible := s.infeasible.set! x oldSet }

/-- z3 `undo_new_stage` — VERBATIM, including the quirk: after
decrementing, z3 resets the assignment of the var it RETURNS to
(`m_assignment.reset(m_xk)` post-decrement), leaving the stage being
exited assigned; the `m_xk == 0` case assigns null with no reset. -/
def undoNewStage : SolverM Unit := do
  match (← get).xk with
  | some 0 => modify fun s => { s with xk := none }
  | some x =>
    let x' := x - 1
    modify fun s => { s with
      xk := some x'
      assignment := s.assignment.erase x' }
  | none => pure ()

/-- z3 `undo_new_level` (the `m_evaluator.pop(1)` is a no-op at
4.12.5). -/
def undoNewLevel : SolverM Unit := do
  modify fun s => { s with scopeLvl := s.scopeLvl - 1 }

/-- z3 `undo_updt_eq`: restore the old eq. Same saved-var vs
undo-time-var argument as `undoSetUpdt`. -/
def undoUpdtEq (x : Var) (oldEq : Option Nat) : SolverM Unit := do
  modify fun s => { s with var2eq := s.var2eq.set! x oldEq }

/-- z3 `undo_until`: pop and dispatch while `pred` and the trail is
nonempty. -/
def undoUntil (pred : SolverM Bool) : SolverM Unit := do
  while (← pred) && !(← get).trail.isEmpty do
    let t := (← get).trail.back! -- nonempty by the loop guard
    match t with
    | .bvarAssignment b => undoBvarAssignment b
    | .infeasibleUpdt x old => undoSetUpdt x old
    | .newStage => undoNewStage
    | .newLevel => undoNewLevel
    | .updtEq x old => undoUpdtEq x old
    modify fun s => { s with trail := s.trail.pop }

/-- z3 `undo_until_size`. -/
def undoUntilSize (oldSize : Nat) : SolverM Unit :=
  undoUntil (do return (← get).trail.size > oldSize)

/-- z3 `undo_until_stage`. -/
def undoUntilStage (newXk : Option Var) : SolverM Unit :=
  undoUntil (do return (← get).xk != newXk)

/-- z3 `undo_until_level`. -/
def undoUntilLevel (newLvl : Nat) : SolverM Unit :=
  undoUntil (do return (← get).scopeLvl > newLvl)

/-- z3 `undo_until_unassigned`. -/
def undoUntilUnassigned (b : Nat) : SolverM Unit :=
  undoUntil (do return (← get).bvalues[b]! != .undef)

/-- z3 `undo_until_empty`. -/
def undoUntilEmpty : SolverM Unit :=
  undoUntil (do return true)

/-! ### value (`:1125`–`:1219` @ 4.12.5)

`Option` threading per the 29.5 ruling: evaluator root paths can
return `none` (the z3 SASSERT-violation image), which propagates;
`value` itself only runs with the atom's max_var assigned (z3
SASSERT) and returns `some .undef` otherwise. -/

/-- z3 `value` (`:1168`): assigned value first, then the evaluator
when the atom's max_var is assigned. -/
def value (l : Literal) : SolverM (Option LBool) := do
  let s ← get
  let val := assignedValue s l
  if val != .undef then return some val
  match s.atoms[l.bvar]? with
  | some (some a) =>
    match a.maxVar with
    | none => return some .undef -- z3: is_assigned(null_var) = false
    | some v =>
      if !(s.assignment.contains v) then return some .undef
      match a with
      | .ineq ia =>
        return some (LBool.ofBool (← liftC (evalIneq ia l.neg s.assignment)))
      | .root ra =>
        match (← liftC (evalRoot ra l.neg s.assignment)) with
        | some b => return some (LBool.ofBool b)
        | none => return none
  | _ => return some .undef

/-- z3 `is_satisfied(clause)` (`:1196`). -/
def isSatisfiedClause (c : Clause) : SolverM (Option Bool) := do
  for l in c.lits do
    match (← value l) with
    | none => return none
    | some .true => return some true
    | _ => pure ()
  return some false

/-- z3 `is_inconsistent` (`:1209`). -/
def isInconsistent (lits : Array Literal) : SolverM (Option Bool) := do
  for l in lits do
    match (← value l) with
    | none => return none
    | some .false => pure ()
    | _ => return some false
  return some true

end Solver

end LeanNonlinearArith.Nlsat
