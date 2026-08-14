import LeanNonlinearArith.Nlsat.IntervalSet
import LeanNonlinearArith.Nlsat.Evaluator
import LeanNonlinearArith.Nlsat.EvaluatorTable
import LeanNonlinearArith.Nlsat.Trace

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

/-- z3 `polynomial::cache` (solver field, `nlsat_solver.cpp:95`) —
memoized `mk_unique`/`psc_chain`/`factor` for explain. Our MPoly is
canonical (eager lex-sorted), so `mk_unique` is the identity and
structural keys cover z3's pointer-identity keys; scans, not hash maps
(atom-table idiom: creation-side, not hot). Reset at reorder (z3's
`m_cache.reset()`, :2408); z3's `reinit_cache` re-priming is a no-op
for us — identity `mk_unique` + on-demand max_var (parity argument:
reinit only re-inserts polys into the unique table and recomputes
cached atom max_vars, both already handled). Engines behind the
tables land in 12d.1b (factor) and 12d.5 (psc_chain). -/
structure ExplainCache where
  pscChains : Array ((MPoly × MPoly × Var) × Array MPoly) := #[]
  factors : Array (MPoly × Array MPoly) := #[]
deriving Inhabited

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
  marks : Array Bool := #[]
  numMarks : Nat := 0
  lemma : Array Literal := #[]
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
  factor : Bool := true            -- nlsat_params `factor` default true (12d's
                                   -- explain; z3's m_factor is never ctor-
                                   -- initialized — updt_params always sets it)
  explainCache : ExplainCache := {}
  -- nla-12d.6b trace egress (F1 of the 2026-08-03 design review):
  -- append-only observation — no control flow ever reads these fields,
  -- which is the parity argument (all 12c/12d behavior unchanged).
  /-- The current resolve round's steps; cleared at each `start:` reset
  (z3's `m_lemma`/`numMarks` reset boundary is the bundling boundary). -/
  pendingTrace : Array TraceStep := #[]
  /-- Per-learned-clause bundles, PARALLEL to `clauses` (the
  `justifications` precedent; `none` for input clauses). Survives
  `delClause` (append-only table — DRAT-style references to
  later-deleted clauses still resolve). -/
  traceBundles : Array (Option TraceBundle) := #[]
  /-- The refutation root: the final round's bundle at the empty-lemma
  UNSAT exit (`resolve`, :993 — no clause is created there). -/
  finalRefutation : Option TraceBundle := none
  /-- F2 extraction-seam snapshot: (atom table, clause table, bundles,
  final bundle) captured in INTERNAL variable order between
  `searchCheck` and `restoreOrder` in `check()` — after `restoreOrder`
  the atom table is renamed back and the solver-level payloads would no
  longer align with it. -/
  refutation : Option (Array (Option Atom) × Array Clause ×
    Array (Option TraceBundle) × TraceBundle) := none
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
    dead := s.dead.push false
    marks := s.marks.push false }
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

/-- z3 `mk_root_atom`: the stored poly is `flip_sign_if_lm_neg`-normalized
(roots unchanged) and `x` is expected to dominate `p`'s variables (z3
SASSERT(x >= max_var(p)); explain maintains this at 12d). Hash-consed
on (kind, x, i, normalized p), as z3's `root_atom_table` (whose hash
uses the `m_cache.mk_unique`d poly — structural equality here covers
the same key). -/
def mkRootAtom (a : RootAtom) : SolverM Nat := do
  let a := { a with p := a.p.flipSignIfLmNeg }
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
    -- unreachable (`maxVar (.bool _) = none` exits above); junk 0
    | .bool _ => 0

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

/-- z3 `atom::is_eq` (EQ or ROOT_EQ). Proxies are not equalities
(search-side unreachable: solver bool vars are `none` in the table). -/
def atomIsEq : Atom → Bool
  | .ineq a => a.kind == .eq
  | .root a => a.kind == .eq
  | .bool _ => false

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
always null under the nra entry — declared non-port.) The trace bundle
array grows in parallel (`none` placeholder; `resolve` flushes the
round's bundle over it at the learned-clause sites). -/
def mkClause (lits : Array Literal) (learned : Bool) : SolverM Nat := do
  let cid := (← get).clauses.size
  let sorted := lits.qsort (litLt (← get))
  modify fun s => { s with clauses := s.clauses.push ⟨sorted, learned, false⟩
                         , traceBundles := s.traceBundles.push none }
  attachClause cid
  return cid

/-! ### Trace egress (nla-12d.6b, F1) -/

/-- Append a trace step. Pure observation: nothing in the search reads
`pendingTrace`, so behavior is byte-identical (the parity argument). -/
def emitTrace (step : TraceStep) : SolverM Unit :=
  modify fun s => { s with pendingTrace := s.pendingTrace.push step }

/-- Flush the round's steps into clause `cid`'s bundle (called right
after the learned-clause `mkClause` sites in `resolve`). -/
def flushTrace (cid : Nat) (lemma : Array Literal) : SolverM Unit :=
  modify fun s => { s with
    traceBundles := s.traceBundles.set! cid (some ⟨s.pendingTrace, lemma⟩)
    pendingTrace := #[] }

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
      -- no arith content to evaluate (z3 evaluates arith atoms only;
      -- proxies get their values from the bvar assignment above)
      | .bool _ => return some .undef
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

/-! ## nla-12c.3 — propagation (`:1264`–`:1428` @ 4.12.5) -/

/-- z3 `R_propagate` (`:1256`): assign `l` true because `l` + the
justifications of `s` is infeasible in the current interpretation. The
lazy justification carries the set's distinct justification literals
(plus `~l` when `include_l`) and clause ids. -/
def rPropagate (l : Literal) (s : IntervalSet) (includeL : Bool := true) :
    SolverM Unit := do
  let (core, clauses) := IntervalSet.justifications s
  let core := if includeL then core.push l.negate else core
  assign l (.lazy core clauses)

/-- z3 `updt_infeasible` (`:1264`): union `s` into `m_infeasible[m_xk]`
(trail-saved). z3 SASSERTs `m_xk != null_var`; the caller
(`processArithClause`) establishes it. -/
def updtInfeasible (set : IntervalSet) : SolverM Unit := do
  match (← get).xk with
  | none => pure () -- z3 SASSERT site: unreachable by construction
  | some x =>
    let oldSet := (← get).infeasible[x]!
    saveSetUpdtTrail x oldSet
    let newSet ← liftC (IntervalSet.mkUnion set oldSet)
    modify fun s => { s with infeasible := s.infeasible.set! x newSet }

/-- z3 `process_boolean_clause` (`:1222`): scan for undef literals;
conflict (false) when none, unit-assign when one, decide otherwise.
The `value(l) != l_true` SASSERT holds because `processClause` checks
`is_satisfied` first. -/
def processBooleanClause (cid : Nat) : SolverM (Option Bool) := do
  let c := (← get).clauses[cid]!
  let mut numUndef := 0
  let mut firstUndef : Option Nat := none
  for i in [:c.lits.size] do
    let l := c.lits[i]!
    match (← value l) with
    | none => return none
    | some .false => pure ()
    | some .undef =>
      numUndef := numUndef + 1
      if firstUndef.isNone then firstUndef := some i
    | some .true => pure () -- z3 SASSERT site: excluded by the caller
  if numUndef == 0 then return some false
  match firstUndef with
  | none => return some false -- unreachable: numUndef > 0
  | some i =>
    if numUndef == 1 then
      assign c.lits[i]! (.clause cid)
    else
      decide c.lits[i]!
  return some true

/-- z3 `process_arith_clause` (`:1317`), the four infeasible-set cases
verbatim: empty ⇒ propagate `l`; full ⇒ propagate `~l`; subset of the
current set ⇒ propagate `l` with it; union-full ⇒ propagate `~l`
justified by the union WITHOUT `l`. Otherwise count undefs: conflict
when zero, unit-assign + `updt_infeasible` when one, decide +
`updt_infeasible` when more (unless a skipped learned clause in lazy
mode). `x` is z3's `m_xk` (SASSERT `m_xk == max_var(cls)`), passed by
`processClause`. -/
def processArithClause (x : Var) (cid : Nat) (satisfyLearned : Bool) :
    SolverM (Option Bool) := do
  let c := (← get).clauses[cid]!
  if !satisfyLearned && (← get).lazyMode ≥ 2 && c.learned then
    return some true -- ignore lemmas in super lazy mode
  let mut numUndef := 0
  let mut firstUndef : Option (Nat × IntervalSet) := none
  for idx in [:c.lits.size] do
    let l := c.lits[idx]!
    match (← value l) with
    | none => return none
    | some .false => pure ()
    | some .true => return some true
    | some .undef =>
      -- z3 SASSERTs max_var(l) == m_xk and atom != nullptr here
      let a := ((← get).atoms[l.bvar]!).get!
      let currSet? ←
        match a with
        | .ineq ia =>
          liftC (infeasibleIntervalsIneq ia l.bvar l.neg (← get).assignment (some cid))
        | .root ra =>
          liftC (infeasibleIntervalsRoot ra l.bvar l.neg (← get).assignment (some cid))
        -- never undef at the arith stage (proxies carry bvar
        -- assignments); none = the evaluator-abort degradation (29.5)
        | .bool _ => pure none
      match currSet? with
      | none => return none -- evaluator abort image (29.5)
      | some currSet =>
        if IntervalSet.isEmpty currSet then
          rPropagate l none
          return some true
        else if IntervalSet.isFull currSet then
          rPropagate l.negate none
        else
          let xkSet := (← get).infeasible[x]!
          if (← liftC (IntervalSet.subset currSet xkSet)) then
            rPropagate l xkSet
            return some true
          else
            let tmp ← liftC (IntervalSet.mkUnion currSet xkSet)
            if IntervalSet.isFull tmp then
              rPropagate l.negate tmp false
            else
              numUndef := numUndef + 1
              if firstUndef.isNone then firstUndef := some (idx, currSet)
  if numUndef == 0 then return some false
  match firstUndef with
  | none => return some false -- unreachable: numUndef > 0
  | some (idx, firstSet) =>
    if numUndef == 1 then
      assign c.lits[idx]! (.clause cid)
      updtInfeasible firstSet
    else if satisfyLearned || !c.learned || (← get).lazyMode == 0 then
      decide c.lits[idx]!
      updtInfeasible firstSet
    else pure () -- skipping learned clause in lazy mode
  return some true

/-- z3 `process_clause` (`:1404`). -/
def processClause (cid : Nat) (satisfyLearned : Bool) : SolverM (Option Bool) := do
  let c := (← get).clauses[cid]!
  match (← isSatisfiedClause c) with
  | none => return none
  | some true => return some true
  | some false =>
    match (← get).xk with
    | none => processBooleanClause cid
    | some x => processArithClause x cid satisfyLearned

/-- z3 `process_clauses` (`:1417`): the violating clause id, or none
when the set was satisfied. (Outer `Option` is the 29.5 abort image.) -/
def processClauses (cids : Array Nat) : SolverM (Option (Option Nat)) := do
  for cid in cids do
    match (← processClause cid false) with
    | none => return none
    | some false => return some (some cid)
    | some true => pure ()
  return some none

/-! ## nla-12c.4 — the search loop, SAT mode (`:1429`–`:1545` @ 4.12.5) -/

/-- z3 `peek_next_bool_var` (`:1429`): advance `m_bk` to the first
unassigned, non-dead, pure-boolean var; null when exhausted (and an
exhausted bk STAYS exhausted — z3's null is UINT_MAX, not 0). -/
def peekNextBoolVar : SolverM Unit := do
  let s ← get
  let mut bk :=
    match s.bk with
    | some b => b
    | none => s.atoms.size -- z3 null_bool_var: the while loop cannot fire
  while bk < s.atoms.size do
    if !s.dead[bk]! && (s.atoms[bk]!).isNone && s.bvalues[bk]! == .undef then
      modify fun s => { s with bk := some bk }
      return
    bk := bk + 1
  modify fun s => { s with bk := none }

/-- z3 `is_satisfied()` (`:1469`): bk exhausted and stage past the last
var. z3's null m_xk is UINT_MAX ≥ num_vars — the `none` branch returns
true to match (that state never reaches the call, but rule 3).
`fix_patch()` is a no-op under the nra entry (m_patch_var always
empty — declared non-port). -/
def isSatisfiedFull : SolverM Bool := do
  let s ← get
  if !s.bk.isNone then return false
  match s.xk with
  | none => return true
  | some x => return x ≥ s.isInt.size

/-- z3 `select_witness` (`:1454`): pick a witness in the complement of
the current infeasible set (the nla-32-re-anchored ladder) and bind
the stage var to it. SASSERT(!is_full) holds by construction. -/
def selectWitness : SolverM Unit := do
  match (← get).xk with
  | none => pure () -- z3 SASSERT site: unreachable by construction
  | some x =>
    match (← liftC (IntervalSet.pickInComplement (← get).infeasible[x]!)) with
    | none => pure () -- z3 SASSERT(!is_full): unreachable by construction
    | some c =>
      modify fun s => { s with assignment := s.assignment.set x c }

/-- z3 `init_search` (`:1642`): unwind everything, reset values and the
assignment. -/
def initSearch : SolverM Unit := do
  undoUntilEmpty
  while (← get).scopeLvl > 0 do
    undoNewLevel
  modify fun s => { s with
    xk := none
    bvalues := s.bvalues.map (fun _ => .undef)
    assignment := #[] }

/-- z3 `search` (`:1485`): stage/level DPLL loop. The resolve
implementation is a parameter — 12c.4 drives it with the stub (SAT
mode first, per the board), 12c.5 wires the real conflict resolution.
Returns l_true/l_false/l_undef as `some _`, or `none` for the 29.5
abort image (z3's throw). -/
def search (resolve : Nat → SolverM (Option Bool)) : SolverM (Option LBool) := do
  modify fun s => { s with bk := some 0, xk := none, conflicts := 0 }
  while true do
    -- stage advance (z3: peek bool var, else next stage)
    match (← get).xk with
    | none =>
      peekNextBoolVar
      if (← get).bk.isNone then newStage
    | some _ => newStage
    if (← isSatisfiedFull) then return some .true
    -- propagation until fixpoint (no conflict), abort, or unsat
    let mut done := false
    while !done do
      let s ← get
      let wl ←
        match s.xk with
        | none =>
          match s.bk with
          | some b => pure s.bwatches[b]!
          | none => pure #[] -- unreachable: bk is set by peek above
        | some x => pure s.watches[x]!
      match (← processClauses wl) with
      | none => return none
      | some (some cid) =>
        match (← resolve cid) with
        | none => return none
        | some false => return some .false
        | some true =>
          if (← get).conflicts ≥ (← get).maxConflicts then
            return some .undef
      | some none => done := true
    -- decide the boolean var (negative-first: literal(bk, true)), or
    -- select the arithmetic witness
    match (← get).xk with
    | none =>
      match (← get).bk with
      | some b =>
        if (← get).bvalues[b]! == .undef then
          decide ⟨b, true⟩
          modify fun s => { s with bk := some (b + 1) }
      | none => pure () -- unreachable by construction
    | some _ => selectWitness
  -- unreachable: the loop only exits via `return` (z3's checkpoint-cancel
  -- exits here by exception — the 29.5 abort image; budgets land at 14)
  return none

/-- The 12c.4 stub resolve: no conflict resolution yet — aborts (the
`none` image) on the first conflict. SAT-mode-first per the board. -/
def stubResolve : Nat → SolverM (Option Bool) := fun _ => pure none

/-! ## nla-12c.5 — conflict resolution (`:1764`–`:2146` @ 4.12.5) -/

/-- The explain boundary (pinned to `explain::operator()(num, lits,
out)` @ 4.12.5): given the core literals of a lazy justification,
return the projection literals to prepend (`resolve_lazy_justification`
itself appends the negated core). The `Option` is the 29.5 abort
image. 12d supplies the real projection. -/
abbrev ExplainFn := Array Literal → SolverM (Option (Array Literal))

/-- Mock explain for solver-level tests: adds nothing — faithful
exactly when the conflict stage has no lower variables to project
(stage-0/univariate conflicts, boolean conflicts). -/
def mockExplain : ExplainFn := fun _ => pure (some #[])
/-- z3 `mark` / `reset_mark` / `is_marked`. -/
def mark (b : Nat) : SolverM Unit :=
  modify fun s => { s with marks := s.marks.set! b true }

def unmark (b : Nat) : SolverM Unit :=
  modify fun s => { s with marks := s.marks.set! b false }

def isMarked (b : Nat) : SolverM Bool := do
  return (← get).marks[b]!

/-- z3's `scoped_reset_marks` destructor: clear everything on exit. -/
def resetAllMarks : SolverM Unit :=
  modify fun s => { s with marks := s.marks.map (fun _ => false), numMarks := 0 }

/-- z3 `reset_marks()`: unmark the lemma's vars and zero the counter
(other marks are cleared by `resetAllMarks` at resolve's exit). -/
def resetMarksLemma : SolverM Unit := do
  for l in (← get).lemma do
    unmark l.bvar
  modify fun s => { s with numMarks := 0 }

/-- z3 `process_antecedent` (`:1764`): collect marked literals into the
lemma or bump the same-level same-stage mark counter. The undef case
is a previous-stage literal false in the current arith interpretation
(z3 SASSERTs `max_var(b) < m_xk` there). -/
def processAntecedent (l : Literal) : SolverM Unit := do
  let s ← get
  let b := l.bvar
  if assignedValue s l == .undef then
    if !(← isMarked b) then
      mark b
      modify fun s => { s with lemma := s.lemma.push l }
    return
  let bLvl := s.levels[b]!
  if !(← isMarked b) then
    mark b
    if bLvl == s.scopeLvl && maxVarB s b == s.xk then
      modify fun s => { s with numMarks := s.numMarks + 1 }
    else
      modify fun s => { s with lemma := s.lemma.push l }

/-- z3 `resolve_clause(b, sz, c)` (`:1797`): process every literal not
on `b`. (z3's assumption join is a declared non-port.) -/
def resolveClause (b : Option Nat) (lits : Array Literal) : SolverM Unit := do
  for l in lits do
    if some l.bvar != b then processAntecedent l

/-- z3 `resolve_lazy_justification` (`:1813`): explain the core, append
the negated core, resolve. The `resolution (.arith …)` marker is
emitted AFTER the explain call so the arith lemma's projection steps
immediately precede it in the round's trace (the 19b consumption
contract). -/
def resolveLazyJustification (explain : ExplainFn) (b : Nat)
    (lits : Array Literal) : SolverM (Option Unit) := do
  match (← explain lits) with
  | none => return none
  | some proj =>
    emitTrace (.resolution (.arith lits proj))
    let mut lazyClause := proj
    for l in lits do
      lazyClause := lazyClause.push l.negate
    resolveClause (some b) lazyClause
    return some ()

/-- z3 `only_literals_from_previous_stages` (`:1871`). -/
def onlyLitsFromPrevStages : SolverM Bool := do
  let s ← get
  return s.lemma.all (fun l => maxVarB s l.bvar != s.xk)

/-- z3 `max_scope_lvl` (`:1884`): max level over the lemma's
assigned-false literals (undef ones are previous-stage and skipped). -/
def maxScopeLvlOfLemma : SolverM Nat := do
  let s ← get
  let mut mx := 0
  for l in s.lemma do
    if assignedValue s l == .false then
      mx := max mx s.levels[l.bvar]!
  return mx

/-- z3 `remove_literals_from_lvl` (`:1911`): pull the same-stage
literals at `lvl` back out of the lemma (they stay marked and become
the new resolution targets). -/
def removeLitsFromLvl (lvl : Nat) : SolverM Unit := do
  let s ← get
  let mut kept : Array Literal := #[]
  for l in s.lemma do
    if assignedValue s l == .false && s.levels[l.bvar]! == lvl
        && maxVarB s l.bvar == s.xk then
      modify fun s => { s with numMarks := s.numMarks + 1 }
    else
      kept := kept.push l
  modify fun s => { s with lemma := kept }

/-- z3 `is_bool_lemma` (`:1933`). -/
def isBoolLemma : SolverM Bool := do
  let s ← get
  return s.lemma.all (fun l => !isArithAtom s l.bvar)

/-- z3 `find_new_level_arith_lemma` (`:1947`): max decision level of
the same-stage literals in the first sz-1 positions; backtrack one
level when there are none. -/
def findNewLevelArithLemma : SolverM Nat := do
  let s ← get
  let mut newLvl : Option Nat := none
  for i in [:s.lemma.size - 1] do
    let l := s.lemma[i]!
    if maxVarB s l.bvar == s.xk then
      let lv := s.levels[l.bvar]!
      newLvl := some (match newLvl with
        | none => lv
        | some cur => max cur lv)
  return newLvl.getD (s.scopeLvl - 1)

/-- z3 `lemma_is_clause` (`:2148`). -/
def lemmaIsClause (cid : Nat) : SolverM Bool := do
  let s ← get
  return s.lemma == s.clauses[cid]!.lits

/-- z3 `resolve` (`:1983`): conflict analysis with the explain
implementation as a parameter (12d). Verbatim structure incl. the
`goto start` loop for conflicts triggered by the learned clause.
Returns `some false` when the empty lemma is derived (UNSAT), `some
true` on resolution, `none` for the 29.5 abort image. -/
def resolve (explain : ExplainFn) (conflictCid : Nat) : SolverM (Option Bool) := do
  let mut conflictCid := conflictCid
  let mut result : Option Bool := none
  let mut done := false
  while !done do
    -- z3 `start:` — fresh conflict analysis round (z3's `m_lemma` reset
    -- is also the trace bundling boundary: aborted rounds self-discard)
    modify fun s => { s with conflicts := s.conflicts + 1, numMarks := 0, lemma := #[]
                           , pendingTrace := #[] }
    resolveClause none (← get).clauses[conflictCid]!.lits
    emitTrace (.resolution (.clause conflictCid))
    let mut top := (← get).trail.size
    let mut foundDecision := false
    let mut aborted := false
    let mut broke := false
    while !broke && !aborted do
      foundDecision := false
      -- trail scan for the marked literals (z3 SASSERT(t.m_kind !=
      -- NEW_STAGE): only same-stage literals are marked)
      while (← get).numMarks > 0 && !aborted do
        if top == 0 then
          aborted := true -- z3 SASSERT(top > 0): unreachable by construction
        else
          match (← get).trail[top - 1]! with
          | .bvarAssignment b =>
            if (← isMarked b) then
              modify fun s => { s with numMarks := s.numMarks - 1 }
              unmark b
              match (← get).justifications[b]! with
              | .clause cid =>
                emitTrace (.resolution (.clause cid))
                resolveClause (some b) (← get).clauses[cid]!.lits
              | .lazy lits _ =>
                match (← resolveLazyJustification explain b lits) with
                | none => aborted := true
                | some () => pure ()
              | .decision =>
                -- z3 SASSERT(m_num_marks == 0)
                foundDecision := true
                let v := (← get).bvalues[b]!
                modify fun s => { s with lemma := s.lemma.push ⟨b, v == .true⟩ }
                emitTrace (.resolution (.decision ⟨b, v == .true⟩))
              | .null => pure () -- z3 UNREACHABLE
          | _ => pure ()
          top := top - 1
      if aborted then broke := true
      else if foundDecision then broke := true
      else if (← onlyLitsFromPrevStages) then broke := true
      else
        -- conflict independent of the current decision, still in this
        -- stage: backtrack to the lemma's max level and continue
        let maxLvl ← maxScopeLvlOfLemma
        removeLitsFromLvl maxLvl
        undoUntilLevel maxLvl
        top := (← get).trail.size
    if aborted then
      result := none
      done := true
    else if (← get).lemma.isEmpty then
      -- empty clause derived: UNSAT — capture the refutation root (F1;
      -- no clause is created here, so the bundle gets a designated field)
      modify fun s => { s with finalRefutation := some ⟨s.pendingTrace, #[]⟩
                             , pendingTrace := #[] }
      result := some false
      done := true
    else
      resetMarksLemma
      if !foundDecision then
        -- case 1: lemma from previous stages only — backjump stages
        let newMaxVar := maxVarLits (← get) (← get).lemma
        undoUntilStage newMaxVar
        let newCid ← mkClause (← get).lemma true
        flushTrace newCid (← get).clauses[newCid]!.lits
        match (← processClause newCid true) with
        | none => result := none; done := true
        | some false => conflictCid := newCid -- z3 `goto start`
        | some true => result := some true; done := true
      else
        -- case 2: decision learned — backjump levels within the stage
        if (← isBoolLemma) then
          undoUntilUnassigned (← get).lemma.back!.bvar
        else
          undoUntilLevel (← findNewLevelArithLemma)
        if (← lemmaIsClause conflictCid) then
          -- the conflict clause itself became asserting
          match (← processClause conflictCid true) with
          | none => result := none; done := true
          | some _ => result := some true; done := true -- z3 VERIFY(...)
        else
          let newCid ← mkClause (← get).lemma true
          flushTrace newCid (← get).clauses[newCid]!.lits
          match (← processClause newCid true) with
          | none => result := none; done := true
          | some false => conflictCid := newCid -- z3 `goto start`
          | some true => result := some true; done := true
  resetAllMarks
  return result

/-! ## nla-12c.6 — variable reorder + check shell (`:1607`–`:1640`,
`:2257`–`:2660` @ 4.12.5)

Reorder is LIVE in the nra path (default true, incremental=false) —
Danielle's 2026-07-31 call: port verbatim. Dead branches omitted
(declared non-ports): `simplify()`/`inline_vars` (flag false),
`shuffle_vars` (random_order false). -/

/-- z3 `is_full_dimensional(literal)` (`:2603`): no equalities or
non-strict inequalities — the case table verbatim. -/
def isFullDimLit (s : Solver) (l : Literal) : Bool :=
  match s.atoms[l.bvar]! with
  | none => true
  | some a =>
    match a with
    | .ineq ia =>
      match ia.kind with
      | .eq => l.neg
      | .lt | .gt => !l.neg
    | .root ra =>
      match ra.kind with
      | .eq => l.neg
      | .lt | .gt => !l.neg
      | .le | .ge => l.neg
    -- no equality/non-strict content (z3's case table is arith-only;
    -- bool vars pass through the `none` arm above search-side)
    | .bool _ => true

/-- z3 `is_full_dimensional()` (`:2638`): over the INPUT clauses. -/
def isFullDimensional (s : Solver) : Bool :=
  s.clauses.all fun c => !c.learned && c.lits.all (isFullDimLit s)

/-- z3 `has_root_atom` (`:2481`). -/
def hasRootAtom (s : Solver) (c : Clause) : Bool :=
  c.lits.any fun l =>
    match s.atoms[l.bvar]! with
    | some (.root _) => true
    | _ => false

/-- z3 `can_reorder` (`:2373`): no root atoms anywhere (`m_patch_var`
is always empty under the nra entry). -/
def canReorder (s : Solver) : Bool :=
  !s.clauses.any (fun c => !c.deleted && hasRootAtom s c)

/-- z3 `var_info_collector` (`:2257`): (max degree, num occurrences)
per var, over all clauses (z3 collects `m_clauses` + `m_learned` —
our single table covers both). -/
def collectVarInfo (s : Solver) : Array (Nat × Nat) := Id.run do
  let n := s.isInt.size
  let mut maxDeg := Array.replicate n 0
  let mut numOcc := Array.replicate n 0
  for c in s.clauses do
    if c.deleted then continue
    for l in c.lits do
      match s.atoms[l.bvar]! with
      | some a =>
        let polys : List MPoly :=
          match a with
          | .ineq ia => ia.factors.map (fun (p, _) => p)
          | .root ra => [ra.p]
          | .bool _ => []  -- no polys (search-side unreachable)
        for p in polys do
          for x in MPoly.vars p do
            numOcc := numOcc.set! x (numOcc[x]! + 1)
            let d := p.degreeIn x
            if d > maxDeg[x]! then maxDeg := maxDeg.set! x d
      | none => pure ()
  return maxDeg.zip numOcc

/-- z3 `reorder_lt` (`:2321`): high degree first, then more
occurrences first, then var id. -/
def reorderLt (info : Array (Nat × Nat)) (x y : Var) : Bool :=
  let (dx, ox) := info[x]!
  let (dy, oy) := info[y]!
  if dx != dy then dx > dy
  else if ox != oy then ox > oy
  else x < y

/-- z3 `reset_watches` (`:2535`): clear the ARITH watch lists (z3 does
not touch `m_bwatches` — boolean watches are var-order independent). -/
def resetWatches : SolverM Unit := do
  modify fun s => { s with watches := s.watches.map (fun _ => #[]) }

/-- z3 `reattach_arith_clauses(m_clauses)` + `(m_learned)` (`:2542`):
re-watch every clause on its (renamed) max_var; pure-boolean clauses
stay in `m_bwatches` and are not reattached, as z3. -/
def reattachArithClauses : SolverM Unit := do
  for cid in [:(← get).clauses.size] do
    let c := (← get).clauses[cid]!
    if !c.deleted then
      match maxVarClause (← get) c with
      | some x =>
        modify fun s => { s with watches := s.watches.modify x (·.push cid) }
      | none => pure ()

/-- z3 `deattach_clause` (`:706`): remove from the watch lists (by
max_var, else max_bvar). -/
def deattachClause (cid : Nat) : SolverM Unit := do
  let c := (← get).clauses[cid]!
  match maxVarClause (← get) c with
  | some x =>
    modify fun s => { s with watches := s.watches.modify x (·.erase cid) }
  | none =>
    modify fun s => { s with bwatches := s.bwatches.modify (maxBvar c) (·.erase cid) }

/-- z3 `del_clause` (`:724`): deattach + mark deleted. Ids stay stable
(z3's `m_cid_gen.recycle` has no port — the append-only table never
recycles, see the 12c representation note). -/
def delClause (cid : Nat) : SolverM Unit := do
  deattachClause cid
  modify fun s => { s with
    clauses := s.clauses.set! cid { s.clauses[cid]! with deleted := true } }

/-- z3 `remove_learned_roots` (`:2465`): learned clauses containing
root atoms are deleted (they would be ill-formed after the rename).
Real deletion now that 12d's explain produces root atoms. -/
def removeLearnedRoots : SolverM Unit := do
  for cid in [:(← get).clauses.size] do
    let c := (← get).clauses[cid]!
    if c.learned && !c.deleted && hasRootAtom (← get) c then
      delClause cid

/-- Rename every atom's polys by `σ` (z3 `m_pm.rename(sz, p)` — ALL
variables, including a root atom's `x`; today unreachable since
`can_reorder` is false when root atoms exist, but rule: cover all
cases). The cells in the store need no renaming (they are
variable-free values). -/
def renameAtoms (σ : Var → Var) : SolverM Unit := do
  modify fun s => { s with
    atoms := s.atoms.map fun
      | none => none
      | some (.ineq a) =>
        some (.ineq { a with factors := a.factors.map fun (p, e) =>
          (p.renameVars σ, e) })
      | some (.root a) =>
        some (.root { a with x := σ a.x, p := a.p.renameVars σ })
      -- defs reference BVARS, not vars — unchanged by var renaming
      -- (never occurs search-side regardless: solver bool vars are none)
      | some (.bool d) => some (.bool d) }

/-- z3 `reorder(sz, p)` (`:2387`): `p` maps internal vars to their new
positions. Verbatim order: reset watches, build the permuted
assignment BEFORE undoing, undo to the null stage, reset the explain
cache (`m_cache.reset()` :2408 — z3's post-rename `reinit_cache`
re-priming is a no-op for us, see `ExplainCache`), remap perms and
is_int, rename polys, swap the assignment in, reattach. -/
def reorder (p : Array Var) : SolverM Unit := do
  removeLearnedRoots
  resetWatches
  let s ← get
  let n := s.isInt.size
  let mut newAsn : Assignment := #[]
  for x in [:n] do
    match s.assignment.get? x with
    | some c => newAsn := newAsn.set p[x]! c
    | none => pure ()
  undoUntilStage none
  modify fun s => { s with explainCache := {} }
  -- m_perm / m_inv_perm update (z3's exact remapping)
  let mut newInv := Array.replicate n 0
  for extX in [:n] do
    newInv := newInv.set! extX p[s.invPerm[extX]!]!
  let mut newPerm := Array.replicate n 0
  for extX in [:n] do
    newPerm := newPerm.set! newInv[extX]! extX
  -- is_int remap
  let mut newIsInt := Array.replicate n false
  for x in [:n] do
    newIsInt := newIsInt.set! p[x]! s.isInt[x]!
  renameAtoms (fun x => p[x]!)
  modify fun s => { s with
    perm := newPerm
    invPerm := newInv
    isInt := newIsInt
    assignment := newAsn }
  reattachArithClauses

/-- z3 `heuristic_reorder` (`:2340`): sort vars by `reorder_lt` and
apply the permutation (`perm[new_order[x]] = x`). -/
def heuristicReorder : SolverM Unit := do
  let s ← get
  let n := s.isInt.size
  let info := collectVarInfo s
  let newOrder := (Array.range n).qsort (reorderLt info)
  let mut perm := Array.replicate n 0
  for x in [:n] do
    perm := perm.set! newOrder[x]! x
  reorder perm

/-- z3 `restore_order` (`:2448`): reorder by the current
(internal → external) permutation. -/
def restoreOrder : SolverM Unit := do
  let p := (← get).perm
  reorder p

/-- z3 `sort_clauses_by_degree`/`sort_watched_clauses` (`:2570`–`:2602`):
each arith watch list sorted by clause degree with the ORIGINAL
POSITION as tiebreak (z3's `degree_lt` verbatim — total order, no
tie-order divergence). -/
def sortWatchedClauses : SolverM Unit := do
  let s ← get
  let deg : Nat → Nat := fun cid => degreeClause s (s.clauses[cid]!)
  for x in [:s.isInt.size] do
    let sorted := s.watches[x]!.mapIdx (fun i cid => (deg cid, i, cid))
      |>.qsort (fun (d1, i1, _) (d2, i2, _) => d1 < d2 || (d1 == d2 && i1 < i2))
      |>.map (·.2.2)
    modify fun s => { s with watches := s.watches.set! x sorted }

/-- z3 `search_check`'s scan (`:1562-1578`): every is_int var whose
assigned value is non-integer, in internal order, with `lo = ⌊v⌋`
computed as z3 does — `int_lt` (integer STRICTLY below; for cells
read off the CURRENT dyadic bound, possibly loose) then the one-step
tighten loop (`while v > lo+1: lo++`) of algebraic-vs-rational
compares (`m_am.gt(v, lo.to_mpq())`; refinement threaded through the
store). z3's defensive `!is_int(vlo) → continue` is vacuous here:
`intLtC` returns `Int` directly. -/
def collectIntBounds : SolverM (Array (Var × Int)) := do
  let s ← get
  let mut bounds : Array (Var × Int) := #[]
  for x in [:s.isInt.size] do
    if s.isInt[x]! then
      match s.assignment.get? x with
      | none => pure ()
      | some c =>
        if !(← liftC (CellStore.isIntC c)) then
          let mut lo ← liftC (CellStore.intLtC c)
          let mut tightening := true
          while tightening do
            let tmp ← liftC (CellStore.fresh (.rat (mkRat (lo + 1) 1)))
            if (← liftC (CellStore.compareC c tmp)) == .gt then
              lo := lo + 1
            else
              tightening := false
          bounds := bounds.push (x, lo)
  return bounds

/-- z3 `search_check`'s per-var branch emission (`:1583-1602`): the
two-literal clause `{¬(x−lo > 0), ¬(x−(lo+1) < 0)}` (`mk_linear`,
`is_even = false`), added INPUT-flagged (`learned = false` — z3's
`mk_clause(…, false, nullptr)`), with the `intBranch` step flushed
into the clause's bundle: the trace carries what z3's nullptr
justification leaves implicit (12e; the clause is derived-by-
integrality, not an input — the walk's contract knows it by the
bundle). -/
def emitIntBranch (x : Var) (lo : Int) : SolverM Unit := do
  let pLo : MPoly := [(1, [(x, 1)]), (-lo, [])]
  let pHi : MPoly := [(1, [(x, 1)]), (-(lo + 1), [])]
  let lLo ← mkIneqLiteral ⟨.gt, [(pLo, false)]⟩
  let lHi ← mkIneqLiteral ⟨.lt, [(pHi, false)]⟩
  emitTrace (.intBranch x lo)
  let cid ← mkClause #[lLo.negate, lHi.negate] false
  flushTrace cid (← get).clauses[cid]!.lits

/-- z3 `search_check` (`:1554-1606`): `search` wrapped in the integer
branch-and-bound loop. After each SAT exit, scan for is_int vars with
non-integer values (`collectIntBounds`); if none, the model stands.
Otherwise `init_search` (learned clauses persist across the restart),
emit one split clause per offending var (`emitIntBranch`), and
re-enter `search`. (12e: no longer real-valued-only — the declared
seam is now the port.) -/
def searchCheck (resolve : Nat → SolverM (Option Bool)) : SolverM (Option LBool) := do
  let mut r ← search resolve
  while r == some LBool.true do
    let bounds ← collectIntBounds
    if bounds.isEmpty then
      break
    initSearch
    for (x, lo) in bounds do
      emitIntBranch x lo
    r ← search resolve
  return r

/-- z3 `check()` (`:1607`): init, full-dimensional flag for 12d's
explain, reorder, watch sorting, search, restore order. -/
def check (resolve : Nat → SolverM (Option Bool)) : SolverM (Option LBool) := do
  initSearch
  modify fun s => { s with fullDimensional := isFullDimensional s }
  let mut reordered := false
  if canReorder (← get) then
    heuristicReorder
    reordered := true
  sortWatchedClauses
  let r ← searchCheck resolve
  -- F2 extraction seam: snapshot the refutation in INTERNAL variable
  -- order before `restoreOrder` renames the atom table back.
  if r == some LBool.false then
    modify fun s => { s with
      refutation := s.finalRefutation.map fun fin =>
        (s.atoms, s.clauses, s.traceBundles, fin) }
  if reordered then
    restoreOrder
  -- z3 SASSERT(r != l_true || check_satisfied(m_clauses)) — the pins
  -- discharge this externally via `modelChecksOut`.
  return r

end Solver

end LeanNonlinearArith.Nlsat
