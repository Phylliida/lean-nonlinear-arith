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

end LeanNonlinearArith.Nlsat.Tests
