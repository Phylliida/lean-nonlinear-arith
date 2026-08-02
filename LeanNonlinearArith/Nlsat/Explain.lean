import LeanNonlinearArith.Nlsat.Solver
import LeanNonlinearArith.Nlsat.MPolyFactor

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
the `max_var` family, `todo_set`, the assumption machinery
(`add_simple_assumption`/`add_assumption`/`ensure_sign`), and — after
12d.1b's `factor_core` port (`Nlsat/MPolyFactor.lean`) — the factor
cache wrapper + `add_zero_assumption`. The psc-chain engine lands
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

/-! ## The factor cache wrapper + add_zero_assumption (:221/:262) -/

/-- z3 `explain::factor` (:221) with the solver-owned memo
(`polynomial_cache::factor` shape; `mk_unique` = identity on canonical
MPoly). Returns the DISTINCT factors — z3's `fs.distinct_factors()`:
the constant and multiplicities are dropped. -/
def factor (p : MPoly) : ExplainM (Array MPoly) := do
  let s ← liftS get
  match s.explainCache.factors.find? (fun (q, _) => q == p) with
  | some (_, fs) => return fs
  | none =>
    let fs := p.factorDistinct
    liftS (modify fun s =>
      { s with explainCache := { s.explainCache with
          factors := s.explainCache.factors.push (p, fs) } })
    return fs

/-- z3 `add_zero_assumption` (:262): factor `p`, keep the factors that
vanish under the current assignment, and emit the NEGATED
multi-factor EQ literal (`p_i1·…·p_im ≠ 0` as a clause literal —
"the case where the needed assumption fails"). z3 SASSERTs at least
one factor vanishes (p itself is zero under the assignment). -/
def addZeroAssumption (p : MPoly) : ExplainM Unit := do
  let fs ← factor p
  let mut zeroFs : List (MPoly × Bool) := []
  for f in fs do
    if (← sign f) == 0 then
      zeroFs := zeroFs ++ [(f, false)]
  let l ← liftS (Solver.mkIneqLiteral ⟨.eq, zeroFs⟩)
  addLiteral l.negate

/-! ## elim_vanishing (:307/:363) -/

/-- z3 `elim_vanishing(p)` (:307): strip leading coefficients that
vanish under the current assignment. Vanishing NON-CONST leading
coefficients become zero assumptions; a nonzero-const lc stops the
walk (the reduct's lc does not vanish). The `k == 0` re-peek walks
DOWN to the reduct's new max var (:318-322); the second `if (k ==
0)` (:348-352, all coeffs vanished ⇒ p := 0) is defensive — the
zero reduct is caught by the `is_const` check first. -/
partial def elimVanishing (p : MPoly) : ExplainM MPoly :=
  match p.maxVar with
  | none => pure p   -- z3 SASSERTs non-const; callers maintain it
  | some x => loop x (p.degreeIn x) p
where
  loop (x : Var) (k : Nat) (p : MPoly) : ExplainM MPoly := do
    if p.asConst?.isSome then return p
    let (x, k) := if k == 0 then
      let x' := p.maxVar.get!
      (x', p.degreeIn x')
    else (x, k)
    let cs := p.coeffsIn x
    -- nonzero_const_coeff: a nonzero constant lc does not vanish
    if (cs[k]!.asConst?.getD 0) != 0 then return p
    let lc := cs[k]!
    if !lc.isZero then
      if (← sign lc) != 0 then return p
      addZeroAssumption lc
    if k == 0 then return []   -- defensive (see doc comment)
    loop x (k - 1) (MPoly.sub p (MPoly.mul (MPoly.ofVarPow x k) lc))

/-- z3 `elim_vanishing(ps)` (:363): per-poly; consts dropped
(compacted in place upstream). -/
def elimVanishingVec (ps : Array MPoly) : ExplainM (Array MPoly) := do
  let mut out : Array MPoly := #[]
  for p in ps do
    let p' ← elimVanishing p
    if !p'.asConst?.isSome then
      out := out.push p'
  return out

/-! ## normalize (:403/:492) -/

/-- z3 `normalize(literal, max)` (:403): eliminate vanishing leading
coefficients (w.r.t. the core's max var) and lower-stage factors from
an ineq literal; eliminated pieces become sign assumptions (negated
clause literals, `add_simple_assumption` polarity). Sign flips
accumulate only for negative ODD factors (:440-442); the rebuilt
literal gets `atom::flip` when `atom_sign < 0` (:468-471) and is
negated iff the original was signed (:472-473). Const-resolution
returns z3's `true_literal ⟨0, false⟩` / `false_literal ⟨0, true⟩`.
Root atoms are NOT normalized (:481). -/
def normalizeLit (l : Literal) (max : Var) : ExplainM Literal := do
  if l.bvar == 0 then return l   -- true_bool_var
  let s ← liftS get
  match s.atoms[l.bvar]? with
  | some (some (.ineq a)) =>
    let mut ps : List (MPoly × Bool) := []
    let mut atomSign : Int := 1
    let mut normalized := false
    let mut ret : Option Literal := none
    for (p0, isEven) in a.factors do
      if ret.isNone then
        let mut p := p0
        if p.maxVar == some max then
          p ← elimVanishing p
        if p.asConst?.isSome || p.maxVar.getD max < max then
          let sg ← sign p
          if !p.asConst?.isSome then
            -- lower-stage factor: justify the elimination
            if sg == 0 then addSimpleAssumption .eq p
            else if isEven then addSimpleAssumption .eq p true
            else if sg < 0 then addSimpleAssumption .lt p
            else addSimpleAssumption .gt p
          if sg == 0 then
            let atomVal := a.kind == .eq
            let litVal := if l.neg then !atomVal else atomVal
            ret := some (if litVal then ⟨0, false⟩ else ⟨0, true⟩)
          else
            if sg < 0 && !isEven then atomSign := -atomSign
            normalized := true
        else
          if p != p0 then normalized := true
          ps := ps ++ [(p, isEven)]
    match ret with
    | some r => return r
    | none =>
      if ps.isEmpty then
        -- all factors eliminated: the residual product is atom_sign
        let atomVal := match a.kind with
          | .eq => false
          | .lt => atomSign < 0
          | .gt => atomSign > 0
        let litVal := if l.neg then !atomVal else atomVal
        return if litVal then ⟨0, false⟩ else ⟨0, true⟩
      else if normalized then
        let newK := if atomSign < 0 then a.kind.flip else a.kind
        let newL ← liftS (Solver.mkIneqLiteral ⟨newK, ps⟩)
        return if l.neg then newL.negate else newL
      else return l
  | _ => return l

/-- z3 `normalize(C, max)` (:492): per-literal; `true_literal` is
dropped; a `false_literal` CLEARS THE WHOLE CORE (:499-502 — the
accumulated assumptions alone imply the conflict). -/
def normalizeCore (C : Array Literal) (max : Var) : ExplainM (Array Literal) := do
  let mut out : Array Literal := #[]
  for l in C do
    let newL ← normalizeLit l max
    if newL == ⟨0, false⟩ then continue
    if newL == falseLiteral then return #[]
    out := out.push newL
  return out

/-! ## add_root_literal family (:717-878) — 12d.4 -/

/-- z3 `mk_linear_root(k, y, i, p, mk_neg)` (:861): a linear root atom
becomes a plain ineq atom on the (possibly negated) poly. -/
def mkLinearRoot5 (k : RootKind) (p : MPoly) (mkNeg : Bool) : ExplainM Unit := do
  let (k', lsign) := k.toIneqSign
  addSimpleAssumption k' (if mkNeg then p.neg else p) lsign

/-- z3 `mk_linear_root(k, y, i, p)` (:742): deg-1 with CONSTANT leading
coefficient (deg-1 polys have a single root; `i` is unused, as
upstream). -/
def mkLinearRoot (k : RootKind) (y : Var) (p : MPoly) : ExplainM Bool := do
  if p.degreeIn y != 1 then return false
  match (p.coeffsIn y)[1]!.asConst? with
  | none => return false
  | some c =>
    if c == 0 then return false   -- z3 SASSERTs; defensive
    mkLinearRoot5 k p (c < 0)
    return true

/-- z3 `mk_plinear_root` (:756): deg-1 with non-const lc — the lc's
sign must be pinned by an `ensure_sign` assumption; fails (⇒ generic
fallback) when the lc vanishes under the assignment. -/
def mkPlinearRoot (k : RootKind) (y : Var) (p : MPoly) : ExplainM Bool := do
  if p.degreeIn y != 1 then return false
  let c := (p.coeffsIn y)[1]!
  let s ← sign c
  if s == 0 then return false
  let _ ← ensureSign c
  mkLinearRoot5 k p (s < 0)
  return true

/-- z3 `mk_quadratic_root` (:787): Thom encoding — the root condition
is witnessed purely by sign literals on {disc, A, 2Ay+B, p}. The
A-vanishing degenerate falls back to `mk_plinear_root` on B·y + C
(:811-812); p_diff goes through `m_pm.normalize` (:803 — ℤ-mode
content strip); a negative discriminant rejects (:806). -/
def mkQuadraticRoot (k : RootKind) (y : Var) (i : Nat) (p : MPoly) : ExplainM Bool := do
  if p.degreeIn y != 2 then return false
  if i != 1 && i != 2 then return false
  let cs := p.coeffsIn y
  let (A, B, C) := (cs[2]!, cs[1]!, cs[0]!)
  let q := (B.mul B).sub ((MPoly.ofInt 4).mul (A.mul C))
  let pDiff := MPoly.managerNormalize none
    (MPoly.add (MPoly.mul (MPoly.smulTerm 2 [] A) (MPoly.ofVar y)) B)
  let sq ← ensureSign q
  if sq < 0 then return false
  let sa ← ensureSign A
  if sa == 0 then
    return ← mkPlinearRoot k y ((B.mul (MPoly.ofVar y)).add C)
  let _ ← ensureSign pDiff
  if sq > 0 then
    let _ ← ensureSign p
  return true

/-- z3 `add_root_literal` (:725): linear encoding, then quadratic,
then the generic root atom via `Solver.mkRootAtom` — always emitted
NEGATED (:733). (`mk_plinear_root` is NOT in this chain upstream —
only reachable via the quadratic degenerate.) -/
def addRootLiteral (k : RootKind) (y : Var) (i : Nat) (p : MPoly) : ExplainM Unit := do
  if !(← mkLinearRoot k y p) && !(← mkQuadraticRoot k y i p) then
    let b ← liftS (Solver.mkRootAtom ⟨k, y, i, p⟩)
    addLiteral ⟨b, true⟩

/-! ## add_cell_lits / all_univ (:899/:975) — 12d.3 -/

/-- z3 `add_cell_lits` (:899): describe the cell of `y` containing the
current value — a single ¬ROOT_EQ literal when `y` hits a root
exactly (immediate return, :936-937), else the tightest root bounds
¬ROOT_GT/¬ROOT_LT (GE/LE under `full_dimensional`), skipping infinite
sides. Root indices are 1-based. `y` is temporarily unassigned for
root isolation (:922). `none` = the 29.5 abort image
(isolate_roots throw: unassigned-var eval). -/
def addCellLits (ps : Array MPoly) (y : Var) : ExplainM (Option Unit) := do
  let s ← liftS get
  let yv := (s.assignment.get? y).get!   -- z3 SASSERTs y assigned
  let mut lowerInf := true
  let mut upperInf := true
  let mut lower : CellId := 0
  let mut upper : CellId := 0
  let mut pLower : MPoly := []
  let mut pUpper : MPoly := []
  let mut iLower : Nat := 0
  let mut iUpper : Nat := 0
  let mut done := false
  for p in ps do
    if !done && p.maxVar == some y then
      match (← liftS (liftC (AnumEval.isolateRootsAt p (s.assignment.erase y)))) with
      | none => return none
      | some roots =>
        for i in [:roots.size] do
          if !done then
            match (← liftS (liftC (CellStore.compareC yv roots[i]!))) with
            | .eq =>
              addRootLiteral .eq y (i + 1) p
              done := true
            | .lt =>
              let better ← if upperInf then pure true
                else liftS (liftC (CellStore.ltC roots[i]! upper))
              if better then
                upperInf := false
                upper := roots[i]!
                pUpper := p
                iUpper := i + 1
            | .gt =>
              let better ← if lowerInf then pure true
                else liftS (liftC (CellStore.ltC lower roots[i]!))
              if better then
                lowerInf := false
                lower := roots[i]!
                pLower := p
                iLower := i + 1
  if done then return some ()
  let fd := (← liftS get).fullDimensional
  if !lowerInf then
    addRootLiteral (if fd then .ge else .gt) y iLower pLower
  if !upperInf then
    addRootLiteral (if fd then .le else .lt) y iUpper pUpper
  return some ()

/-- z3 `all_univ` (:975): every poly is univariate in `x` with `x` its
max var. -/
def allUniv (ps : Array MPoly) (x : Var) : Bool :=
  ps.all fun p => p.maxVar == some x && p.varDegrees.size == 1

end Explain

end LeanNonlinearArith.Nlsat
