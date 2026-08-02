import LeanNonlinearArith.Nlsat.Solver

/-!
# nla-12d — explain: the projection port (z3 `nlsat_explain.cpp` @ **4.12.5**)

Source text: `git show z3-4.12.5:src/nlsat/nlsat_explain.{h,cpp}` (1914
lines — levelwise does not exist at 4.12.5; the classic
Jovanović–de Moura projection is the whole file). Untrusted
search-side; the trusted checker is nla-19a's `Nlsat/Check.lean`.

**Interface audit (12d.0, BOARD nla-12d):** the nra path touches
explain only via the flags + `operator()` + `reset`
(nlsat_solver.cpp:239/:276/:1611/:1828). Flag values on our path:
`simplify_cores=true`, `minimize_cores=false`, `factor=true`,
`full_dimensional=dynamic`, `signed_project=false`. Declared
non-ports (dead on the nra path at 4.12.5): the minimize cluster
(:1405-1472), the signed_project cluster (:1604-1806), maximize
(:1808), public `project(var,…)` (:1503), `keep_p_x` (:559),
`test_root_literal` (:1879), display/pp printers.

**Slice 12d.1 (this file, so far):** the explain monad + per-call
state, `add_literal`/`reset_already_added`, `sign`, `collect_polys`,
the `max_var` family, `todo_set`, and the assumption machinery
(`add_simple_assumption`/`add_assumption`/`ensure_sign`). Deferred:
`add_zero_assumption` (:262) needs the factor engine — the
multivariate `factor_core` port (iccp/Yun/deg-1/deg-2/univ pieces,
`sqrt` attempt, distinct-factors with the constant dropped) lands as
**12d.1b** behind `ExplainCache.factors`; the psc-chain engine lands
with 12d.5 behind `ExplainCache.pscChains`.

**Clause polarity convention (load-bearing):** explain's output is a
theory-lemma CLAUSE, so every assumption appears NEGATED —
`add_simple_assumption` emits `literal(b, !sign)` (:290), root
literals are always emitted negated (:733). The exception is
`mk_linear_root` encodings, which fold the negation into the
kind-remap (:869-878, 12d.4).
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

namespace Explain

/-! ## Per-call state and the explain monad

z3's `imp` persists across calls, but all of its mutable fields are
scratch reset per `operator()` call (`m_result` + the dedup bits,
`m_todo`, `m_ps*` buffers, `m_core1/2`) — the only cross-call state is
the solver-owned `m_cache` (our `Solver.explainCache`) and the flags
(on `Solver`). So per-call state is a local record threaded through
`StateT` over `SolverM`. -/

structure ExplainState where
  /-- `*m_result` contents (the projection literals emitted so far). -/
  result : Array Literal := #[]
  /-- `m_already_added_literal`: emitted literal indexes (scan dedup,
  atom-table idiom — result vectors are conflict-core sized). -/
  alreadyAdded : Array Nat := #[]
deriving Inhabited

abbrev ExplainM := StateT ExplainState SolverM

/-- Run an explain computation from the empty solver state (test
ergonomics, `Solver.run'` analogue). -/
def run' (f : ExplainM α) : α := ((f.run {}).run Solver.empty).1.1

/-- Lift a solver computation into the explain monad. -/
def liftS (f : SolverM α) : ExplainM α := fun st => do
  let a ← f
  return (a, st)

/-! ## `add_literal` / `reset_already_added` (:183/:199) -/

/-- z3's `false_literal` (`~true_literal`; bvar 0 is the true bvar,
`Solver.mkTrueBvar`). -/
def falseLiteral : Literal := ⟨0, true⟩

/-- z3 `add_literal` (`:183`): dedup by literal index; `false_literal`
dropped silently. z3 SASSERTs `l != true_literal` — debug-only;
release would push it, and we keep the release behavior (only
`false_literal` is dropped). -/
def addLiteral (l : Literal) : ExplainM Unit := do
  if l == falseLiteral then return
  let st ← get
  if st.alreadyAdded.contains l.index then return
  set { st with alreadyAdded := st.alreadyAdded.push l.index
              , result := st.result.push l }

/-- z3 `reset_already_added` (`:199`): bulk-clear the dedup set (z3
clears the bit per emitted literal — same net state). -/
def resetAlreadyAdded : ExplainM Unit :=
  modify fun st => { st with alreadyAdded := #[] }

/-! ## `sign` / `collect_polys` / `max_var` (:211/:241/:510-554) -/

/-- z3 `sign` (`:211`): `eval_sign_at` under the current assignment.
z3 SASSERTs `max_var(p)` is assigned; the callers (ensure_sign,
add_cell_lits, psc) maintain that invariant. -/
def sign (p : MPoly) : ExplainM Int := do
  let s ← liftS get
  liftS (liftC (AnumEval.evalSignAt p s.assignment))

/-- z3 `collect_polys` (`:241`): all polys occurring in the literals —
ineq atoms contribute every factor, root atoms their single poly.
z3 SASSERTs every literal is arith (the cores reaching
`resolve_lazy_justification` are); pure-boolean bvars are skipped here
(release z3 would null-deref — no behavior to match; the invariant is
documented). -/
def collectPolys (lits : Array Literal) : ExplainM (Array MPoly) := do
  let s ← liftS get
  let mut ps : Array MPoly := #[]
  for l in lits do
    match s.atoms[l.bvar]? with
    | some (some (.ineq a)) =>
      for (p, _) in a.factors do ps := ps.push p
    | some (some (.root a)) => ps := ps.push a.p
    | _ => pure ()
  return ps

/-- z3 `max_var(ps)` (`:515`): `null_var` on empty. z3 SASSERTs every
member is non-const, but release-mode `UINT_MAX` flows through the max
— a const member poisons the result to `null_var` (replicated, per
the null-poisoning rule). -/
def maxVarPolys (ps : Array MPoly) : Option Var :=
  ps.foldl (fun acc p =>
    match acc, p.maxVar with
    | none, _ => none
    | some _, none => none
    | some a, some b => some (max a b))
    (if ps.isEmpty then none else some 0)

/-- z3 `max_var(sz, ls)` (`:541`) is `Solver.maxVarLits` — same
fold (skip pure booleans, const-atom poison to `null_var`). -/
def maxVarLits (s : Solver) (lits : Array Literal) : Option Var :=
  Solver.maxVarLits s lits

/-! ## `todo_set` (:49-117) -/

/-- z3 `m_cache.mk_unique`: the identity on our canonical MPoly —
z3 hash-conses so `pm.id` gives stable dedup keys; structural
equality on the canonical form IS the same key (see
`Solver.ExplainCache`). -/
def mkUnique (p : MPoly) : MPoly := p

/-- z3 `todo_set`: dedup'd polynomial worklist (`m_set` + `m_in_set`
collapsed — structural dedup). -/
structure TodoSet where
  polys : Array MPoly := #[]
deriving Inhabited

namespace TodoSet

/-- z3 `todo_set::reset` (`:56`). -/
def reset : TodoSet := {}

/-- z3 `todo_set::insert` (`:65`): `mk_unique`, then dedup. -/
def insert (t : TodoSet) (p : MPoly) : TodoSet :=
  let p := mkUnique p
  if t.polys.contains p then t else ⟨t.polys.push p⟩

/-- z3 `todo_set::empty` (`:75`). -/
def empty (t : TodoSet) : Bool := t.polys.isEmpty

/-- z3 `todo_set::max_var` (`:78`): `null_var` on empty; const members
poison as in `maxVarPolys`. -/
def maxVar (t : TodoSet) : Option Var := maxVarPolys t.polys

/-- z3 `todo_set::remove_max_polys` (`:95`): the maximal-stage polys
move out (their `max_var == x` — with a const-poisoned set, `x =
null_var` and exactly the const polys match, as z3's `y == x` with
`y = null_var`). Returns (max var, removed polys, remaining set). -/
def removeMaxPolys (t : TodoSet) : Option Var × Array MPoly × TodoSet := Id.run do
  let x := t.maxVar
  let mut maxPolys : Array MPoly := #[]
  let mut rest : Array MPoly := #[]
  for p in t.polys do
    if p.maxVar == x then maxPolys := maxPolys.push p
    else rest := rest.push p
  return (x, maxPolys, ⟨rest⟩)

end TodoSet

/-! ## Assumption machinery (:286/:294/:822) -/

/-- z3 `add_simple_assumption` (`:286`): single-factor ineq atom
(`is_even = false`), literal `(b, !sign)` — with default `sign=false`
the NEGATED literal (assumptions appear negated in the output clause:
the lemma covers the case where the assumption fails). -/
def addSimpleAssumption (k : IneqKind) (p : MPoly) (sign : Bool := false) :
    ExplainM Unit := do
  let b ← liftS (Solver.mkIneqAtom ⟨k, [(p, false)]⟩)
  addLiteral ⟨b, !sign⟩

/-- z3 `add_assumption` (`:294`): pass-through to `add_simple_assumption`
(upstream carries `// TODO: factor`). -/
def addAssumption (k : IneqKind) (p : MPoly) (sign : Bool := false) :
    ExplainM Unit :=
  addSimpleAssumption k p sign

/-- z3 `ensure_sign` (`:822`, the ACTIVE `#else` branch — the factoring
`#if 0` branch is dead upstream): assert `p`'s sign under the current
assignment as a (negated) sign literal; consts emit nothing. Returns
the sign. -/
def ensureSign (p : MPoly) : ExplainM Int := do
  let s ← sign p
  if !p.asConst?.isSome then
    addSimpleAssumption (if s == 0 then .eq else if s < 0 then .lt else .gt) p
  return s

end Explain

end LeanNonlinearArith.Nlsat
