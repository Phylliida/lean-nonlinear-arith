import LeanNonlinearArith.Nlsat.Explain

/-!
# nla-12d.1 tests — explain scaffold pins

`add_literal` (dedup + false_literal drop), `reset_already_added`,
`todo_set` (insert/reset/max_var/remove_max_polys incl. the const
poison), `collect_polys`, `maxVarPolys`, and the assumption machinery
(`add_simple_assumption`/`add_assumption`/`ensure_sign` with its
clause-polarity convention). Store discipline: one `ExplainM`
computation per scenario (`Explain.run'`).
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Solver hiding run'
open LeanNonlinearArith.Nlsat.Explain hiding maxVarLits

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def p01 : MPoly := MPoly.add x0 x1
private def c5 : MPoly := MPoly.ofInt 5

/-! ## add_literal / reset_already_added (`:183`/`:199`) -/

-- dedup by literal index; ¬l kept alongside l (different index);
-- false_literal ⟨0, true⟩ dropped silently; ⟨0, false⟩ kept (z3's
-- SASSERT against true_literal is debug-only — release pushes it)
#guard Explain.run' (do
  addLiteral ⟨1, false⟩
  addLiteral ⟨1, false⟩
  addLiteral ⟨1, true⟩
  addLiteral ⟨0, true⟩
  addLiteral ⟨0, false⟩
  return (← get).result == #[⟨1, false⟩, ⟨1, true⟩, ⟨0, false⟩])

-- after reset_already_added the same literal can be emitted again
#guard Explain.run' (do
  addLiteral ⟨2, false⟩
  resetAlreadyAdded
  addLiteral ⟨2, false⟩
  return (← get).result == #[⟨2, false⟩, ⟨2, false⟩])

/-! ## todo_set (`:49-117`) -/

-- insert dedups structurally (mk_unique = identity on canonical MPoly)
#guard (TodoSet.insert (TodoSet.insert {} x0) x0).polys.size == 1
#guard (TodoSet.insert (TodoSet.insert {} x0) p01).polys.size == 2
#guard TodoSet.reset.polys.isEmpty && TodoSet.empty {}

-- max_var: empty → null_var; maximal variable otherwise
#guard TodoSet.maxVar {} == none
#guard TodoSet.maxVar (TodoSet.insert (TodoSet.insert {} x0) p01) == some 1

-- remove_max_polys: maximal-stage polys move out, the rest stay
#guard
  let t := TodoSet.insert (TodoSet.insert {} x0) p01
  let (x, maxPs, rest) := t.removeMaxPolys
  x == some 1 && maxPs == #[p01] && rest.polys == #[x0]

-- const-poisoned set: x = null_var and exactly the const polys match
-- (z3's `y == x` with y = null_var = UINT_MAX)
#guard
  let t := TodoSet.insert (TodoSet.insert {} x0) c5
  let (x, maxPs, rest) := t.removeMaxPolys
  x == none && maxPs == #[c5] && rest.polys == #[x0]

/-! ## collect_polys / maxVarPolys (`:241`/`:515`) -/

-- ineq atoms contribute every factor (parity tags ignored), root atoms
-- their (normalized) single poly; literal order preserved
#guard Explain.run' (do
  Solver.init
  let b1 ← liftS (mkIneqAtom ⟨.lt, [(p01, false), (x0, true)]⟩)
  let b2 ← liftS (mkRootAtom ⟨.eq, 1, 2, p01⟩)
  let ps ← collectPolys #[⟨b1, false⟩, ⟨b2, true⟩]
  return ps == #[p01, x0, p01])

-- pure-boolean literals are skipped (z3 SASSERTs arith-only cores)
#guard Explain.run' (do
  Solver.init
  let b ← liftS mkBoolVar
  let ps ← collectPolys #[⟨b, false⟩]
  return ps == #[])

-- maxVarPolys: empty → null_var; const member poisons to null_var
#guard maxVarPolys #[] == none
    && maxVarPolys #[x0] == some 0
    && maxVarPolys #[x0, p01] == some 1
    && maxVarPolys #[x0, c5] == none
    && maxVarPolys #[c5, x0] == none

/-! ## assumption machinery (`:286`/`:294`/`:822`) -/

-- add_simple_assumption: single-factor atom, NEGATED literal by
-- default (assumptions appear negated in the output clause)
#guard Explain.run' (do
  Solver.init
  addSimpleAssumption .gt p01
  let st ← get
  let s ← liftS get
  return st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(p01, false)]⟩))

-- add_assumption with sign=true: the positive literal (assumption
-- `p ≠ 0` ⇒ clause literal is `p = 0`)
#guard Explain.run' (do
  Solver.init
  addAssumption .eq p01 true
  return (← get).result == #[⟨1, false⟩])

-- ensure_sign at x0 := 3 on x0 − 2: sign 1, negated GT literal;
-- repeated call dedups (same atom, same literal)
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c })
  let s1 ← ensureSign (MPoly.add x0 (MPoly.ofInt (-2)))
  let s2 ← ensureSign (MPoly.add x0 (MPoly.ofInt (-2)))
  let st ← get
  let s ← liftS get
  return s1 == 1 && s2 == 1 && st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(MPoly.add x0 (MPoly.ofInt (-2)), false)]⟩))

-- ensure_sign at x0 := 2 (zero sign ⇒ EQ) and x0 := 1 (negative ⇒ LT)
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 2 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c })
  let sg ← ensureSign (MPoly.add x0 (MPoly.ofInt (-2)))
  let s ← liftS get
  return sg == 0 && (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.eq, [(MPoly.add x0 (MPoly.ofInt (-2)), false)]⟩))

#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c })
  let sg ← ensureSign (MPoly.add x0 (MPoly.ofInt (-2)))
  let s ← liftS get
  return sg == -1 && (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.lt, [(MPoly.add x0 (MPoly.ofInt (-2)), false)]⟩))

-- consts emit nothing (z3's `!is_const(p)` guard), sign still returned
#guard Explain.run' (do
  Solver.init
  let s1 ← ensureSign c5
  let s2 ← ensureSign (MPoly.ofInt (-7))
  let s3 ← ensureSign MPoly.zero
  return s1 == 1 && s2 == -1 && s3 == 0 && (← get).result == #[])

end LeanNonlinearArith.Nlsat.Tests
