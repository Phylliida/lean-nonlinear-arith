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

/-! ## elim_vanishing / normalize (12d.2) -/

private def oneM : MPoly := MPoly.ofInt 1

-- elim_vanishing: (x0−1)·x1² + x1 + 1 at x0 := 1 — the vanishing lc
-- becomes a zero assumption, result is x1 + 1 (z3's Example 1 shape)
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let p := MPoly.add (MPoly.smulTerm 1 [(1,2)] (MPoly.sub x0 oneM)) (MPoly.add x1 oneM)
  let p' ← elimVanishing p
  let st ← get
  let s ← liftS get
  return p' == MPoly.add x1 oneM
    && st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.eq, [(MPoly.sub x0 oneM, false)]⟩))

-- all coefficients vanish ⇒ the zero polynomial
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let p' ← elimVanishing (MPoly.smulTerm 1 [(1,1)] (MPoly.sub x0 oneM))
  return p' == MPoly.zero && (← get).result == #[⟨1, true⟩])

-- the walk-down re-peek: (x0−1)·x1 + (x0−1) at x0 := 1 — after x1's
-- coeff vanishes, x0 is re-peeked; its lc (1) is nonzero const ⇒ stop
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let p := MPoly.add (MPoly.smulTerm 1 [(1,1)] (MPoly.sub x0 oneM)) (MPoly.sub x0 oneM)
  let p' ← elimVanishing p
  return p' == MPoly.sub x0 oneM && (← get).result == #[⟨1, true⟩])

-- elim_vanishing(ps): zero results dropped
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let out ← elimVanishingVec #[MPoly.add x1 oneM,
    MPoly.smulTerm 1 [(1,1)] (MPoly.sub x0 oneM)]
  return out == #[MPoly.add x1 oneM] && (← get).result == #[⟨1, true⟩])

-- normalize, z3's Example 2 VERBATIM: (x1+2)·(x0−1) > 0 with max = x1
-- and x0 := 0 ⇒ returns (x1+2) < 0 with assumption x0−1 < 0 (negated
-- in the clause); kind flipped by the negative odd factor
#guard Explain.run' (do
  Solver.init
  let c0 ← liftS (liftC (CellStore.fresh (.rat 0 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c0 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.add x1 (MPoly.ofInt 2), false),
    (MPoly.sub x0 oneM, false)]⟩)
  let newL ← normalizeLit ⟨b, false⟩ 1
  let st ← get
  let s ← liftS get
  return st.result == #[⟨2, true⟩]
    && s.atoms[2]! == some (.ineq ⟨.lt, [(MPoly.sub x0 oneM, false)]⟩)
    && newL == ⟨3, false⟩
    && s.atoms[3]! == some (.ineq ⟨.lt, [(MPoly.add x1 (MPoly.ofInt 2), false)]⟩))

-- same atom at x0 := 3: GT assumption, no flip (positive factor)
#guard Explain.run' (do
  Solver.init
  let c3 ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c3 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.add x1 (MPoly.ofInt 2), false),
    (MPoly.sub x0 oneM, false)]⟩)
  let newL ← normalizeLit ⟨b, false⟩ 1
  let s ← liftS get
  return (← get).result == #[⟨2, true⟩]
    && s.atoms[2]! == some (.ineq ⟨.gt, [(MPoly.sub x0 oneM, false)]⟩)
    && newL == ⟨3, false⟩
    && s.atoms[3]! == some (.ineq ⟨.gt, [(MPoly.add x1 (MPoly.ofInt 2), false)]⟩))

-- zero factor ⇒ false_literal (product is 0, GT is false)
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.add x1 (MPoly.ofInt 2), false),
    (MPoly.sub x0 oneM, false)]⟩)
  let newL ← normalizeLit ⟨b, false⟩ 1
  let s ← liftS get
  return newL == ⟨0, true⟩
    && (← get).result == #[⟨2, true⟩]
    && s.atoms[2]! == some (.ineq ⟨.eq, [(MPoly.sub x0 oneM, false)]⟩))

-- even factor eliminated with the p ≠ 0 assumption shape (positive EQ
-- clause literal, add_simple_assumption sign=true)
#guard Explain.run' (do
  Solver.init
  let c3 ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c3 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.sub x0 oneM, true), (x1, false)]⟩)
  let newL ← normalizeLit ⟨b, false⟩ 1
  let s ← liftS get
  return (← get).result == #[⟨2, false⟩]
    && s.atoms[2]! == some (.ineq ⟨.eq, [(MPoly.sub x0 oneM, false)]⟩)
    && newL == ⟨3, false⟩)

-- all factors eliminated (ps empty): residual product is atom_sign —
-- two positives ⇒ true_literal
#guard Explain.run' (do
  Solver.init
  let c3 ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c3 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.sub x0 oneM, false),
    (MPoly.sub x0 (MPoly.ofInt 2), false)]⟩)
  let newL ← normalizeLit ⟨b, false⟩ 1
  return newL == ⟨0, false⟩ && (← get).result.size == 2)

-- normalize(C): true_literal dropped, false_literal clears the core
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let b1 ← liftS (mkIneqAtom ⟨.eq, [(MPoly.sub x0 oneM, false)]⟩)  -- resolves true
  let b2 ← liftS (mkIneqAtom ⟨.gt, [(x1, false)]⟩)                 -- kept as-is
  let out ← normalizeCore #[⟨b1, false⟩, ⟨b2, false⟩] 1
  -- the assumption reuses b1's atom (hash-consed) — literal ⟨1, true⟩
  return out == #[⟨b2, false⟩] && (← get).result == #[⟨1, true⟩])

#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let b1 ← liftS (mkIneqAtom ⟨.gt, [(MPoly.sub x0 oneM, false)]⟩)  -- resolves false
  let b2 ← liftS (mkIneqAtom ⟨.gt, [(x1, false)]⟩)
  let out ← normalizeCore #[⟨b1, false⟩, ⟨b2, false⟩] 1
  return out == #[])

-- root atoms are NOT normalized
#guard Explain.run' (do
  Solver.init
  let b ← liftS (mkRootAtom ⟨.gt, 1, 1, p01⟩)
  let newL ← normalizeLit ⟨b, true⟩ 1
  return newL == ⟨b, true⟩ && (← get).result == #[])

/-! ## add_root_literal family (12d.4) -/

-- linear, const lc: root becomes a plain ineq atom (negated literal)
#guard Explain.run' (do
  Solver.init
  addRootLiteral .gt 0 1 (MPoly.sub (MPoly.smulTerm 2 [] x0) (MPoly.ofInt 6))
  let s ← liftS get
  return (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt,
      [(MPoly.sub (MPoly.smulTerm 2 [] x0) (MPoly.ofInt 6), false)]⟩))

-- negative const lc: poly negated first (mk_neg), same atom shape
#guard Explain.run' (do
  Solver.init
  addRootLiteral .gt 0 1 (MPoly.add (MPoly.smulTerm (-2) [] x0) (MPoly.ofInt 6))
  let s ← liftS get
  return (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt,
      [(MPoly.sub (MPoly.smulTerm 2 [] x0) (MPoly.ofInt 6), false)]⟩))

-- ROOT_LE remap: (GT, negated) ⇒ POSITIVE literal on the GT atom
#guard Explain.run' (do
  Solver.init
  addRootLiteral .le 0 1 (MPoly.sub (MPoly.smulTerm 2 [] x0) (MPoly.ofInt 6))
  let s ← liftS get
  return (← get).result == #[⟨1, false⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt,
      [(MPoly.sub (MPoly.smulTerm 2 [] x0) (MPoly.ofInt 6), false)]⟩))

-- quadratic with A vanishing at the sample ⇒ plinear fallback on
-- B·y + C; emissions in order: disc sign, A sign, linear encoding
#guard Explain.run' (do
  Solver.init
  let c0 ← liftS (liftC (CellStore.fresh (.rat 0 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c0 })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let p := MPoly.add (MPoly.smulTerm 1 [(1,2)] x0)
    (MPoly.sub x1 oneM)
  addRootLiteral .eq 1 1 p
  let st ← get
  let s ← liftS get
  return st.result == #[⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(MPoly.add oneM (MPoly.smulTerm 4 [] x0), false)]⟩)
    && s.atoms[2]! == some (.ineq ⟨.eq, [(x0, false)]⟩)
    && s.atoms[3]! == some (.ineq ⟨.eq, [(MPoly.sub x1 oneM, false)]⟩))

-- full Thom: emissions are sign literals on {p_diff (CONTENT-STRIPPED
-- by m_pm.normalize!), p}; disc/A are const here ⇒ no literals
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c1 })
  addRootLiteral .lt 1 1 (MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2))
  let st ← get
  let s ← liftS get
  return st.result == #[⟨1, true⟩, ⟨2, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(x1, false)]⟩)
    && s.atoms[2]! == some (.ineq ⟨.lt,
      [(MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2), false)]⟩))

-- generic fallback (deg ≥ 3): root atom, negated literal
#guard Explain.run' (do
  Solver.init
  addRootLiteral .lt 1 1 (MPoly.sub (MPoly.pw x1 3) (MPoly.ofInt 2))
  let s ← liftS get
  return (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.root ⟨.lt, 1, 1,
      MPoly.sub (MPoly.pw x1 3) (MPoly.ofInt 2)⟩))

-- deg-1 with non-const lc: mk_plinear is NOT in add_root_literal's
-- chain ⇒ generic root atom (z3 :725-735)
#guard Explain.run' (do
  Solver.init
  let c3 ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c3 })
  addRootLiteral .gt 1 1 (MPoly.add (MPoly.mul x0 x1) oneM)
  let s ← liftS get
  return (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.root ⟨.gt, 1, 1,
      MPoly.add (MPoly.mul x0 x1) oneM⟩))

/-! ## add_cell_lits (12d.3) -/

private def x1sqM2 : MPoly := MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2)

-- exact-root hit: y = √2 is root 2 of x1²−2 ⇒ single Thom emission
-- round (p_diff GT, p EQ), NO bounds (immediate return :936-937)
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.root #[-2, 0, 1] 1 2 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c })
  let r ← addCellLits #[x1sqM2] 1
  let st ← get
  let s ← liftS get
  return r == some ()
    && st.result == #[⟨1, true⟩, ⟨2, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(x1, false)]⟩)
    && s.atoms[2]! == some (.ineq ⟨.eq, [(x1sqM2, false)]⟩))

-- two-sided cell (y = 1 between −√2 and √2): bound literals from both
-- sides — and the Thom emissions DEDUP across the two add_root_literal
-- calls (same p_diff/p sign atoms)
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c })
  let r ← addCellLits #[x1sqM2] 1
  let st ← get
  let s ← liftS get
  return r == some ()
    && st.result == #[⟨1, true⟩, ⟨2, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(x1, false)]⟩)
    && s.atoms[2]! == some (.ineq ⟨.lt, [(x1sqM2, false)]⟩))

-- lower-only (y = 3): one bound; p's sign is positive ⇒ GT on p
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c })
  let r ← addCellLits #[x1sqM2] 1
  let st ← get
  let s ← liftS get
  return r == some ()
    && st.result == #[⟨1, true⟩, ⟨2, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(x1, false)]⟩)
    && s.atoms[2]! == some (.ineq ⟨.gt, [(x1sqM2, false)]⟩))

-- upper-only (y = −3): p_diff negative ⇒ LT on it; p positive ⇒ GT
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat (-3) : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c })
  let r ← addCellLits #[x1sqM2] 1
  let st ← get
  let s ← liftS get
  return r == some ()
    && st.result == #[⟨1, true⟩, ⟨2, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.lt, [(x1, false)]⟩)
    && s.atoms[2]! == some (.ineq ⟨.gt, [(x1sqM2, false)]⟩))

-- linear cell bounds: plain ineq encoding; full_dimensional flips
-- GT→GE (remapped to a POSITIVE LT literal by mk_linear_root)
#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c })
  let r ← addCellLits #[MPoly.sub x1 (MPoly.ofInt 2)] 1
  let s ← liftS get
  return r == some ()
    && (← get).result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(MPoly.sub x1 (MPoly.ofInt 2), false)]⟩))

#guard Explain.run' (do
  Solver.init
  let c ← liftS (liftC (CellStore.fresh (.rat 3 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c
                                , fullDimensional := true })
  let r ← addCellLits #[MPoly.sub x1 (MPoly.ofInt 2)] 1
  let s ← liftS get
  return r == some ()
    && (← get).result == #[⟨1, false⟩]
    && s.atoms[1]! == some (.ineq ⟨.lt, [(MPoly.sub x1 (MPoly.ofInt 2), false)]⟩))

-- all_univ
#guard allUniv #[x0, MPoly.add (MPoly.mul x0 x0) oneM] 0
    && !allUniv #[MPoly.mul x0 x1] 1
    && !allUniv #[x0] 1

/-! ## psc / add_lc / add_factors / project (12d.5) -/

-- psc chain reaching a nonzero const ⇒ done immediately, no emissions
#guard Explain.run' (do
  Solver.init
  psc (MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2)) (MPoly.smulTerm 2 [] x1) 1
  let st ← get
  return st.result == #[] && st.todo.empty)

-- vanishing psc ⇒ zero assumption on the factor (content −4 dropped:
-- factor of −4·x0 is [−x0])
#guard Explain.run' (do
  Solver.init
  let c0 ← liftS (liftC (CellStore.fresh (.rat 0 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c0 })
  psc (MPoly.sub (MPoly.mul x1 x1) x0) (MPoly.smulTerm 2 [] x1) 1
  let st ← get
  let s ← liftS get
  return st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.eq, [(MPoly.neg x0, false)]⟩))

-- surviving psc ⇒ add_factors into the todo (factor of −8·x0² = [x0])
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  psc (MPoly.sub (MPoly.mul x1 x1) (MPoly.smulTerm 2 [] (MPoly.mul x0 x0)))
    (MPoly.smulTerm 2 [] x1) 1
  let st ← get
  return st.result == #[] && st.todo.polys == #[x0])

-- add_lc: non-const lcs into the todo; const lcs skipped
#guard Explain.run' (do
  Solver.init
  addLc #[MPoly.add (MPoly.smulTerm 1 [(1,2)] x0) x1,
    MPoly.smulTerm 2 [] (MPoly.mul x1 x1)] 1
  return (← get).todo.polys == #[x0])

-- psc chain memoization
#guard Explain.run' (do
  Solver.init
  let p := MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2)
  let q := MPoly.smulTerm 2 [] x1
  let S1 ← pscChainCached p q 1
  let S2 ← pscChainCached p q 1
  let s ← liftS get
  return S1 == S2 && S1 == #[MPoly.ofInt (-8)]
    && s.explainCache.pscChains.size == 1)

-- project: two-stage projection of {x1² − x0} at x0 := 4 — psc work
-- produces x0 for the lower stage, then cell lits bracket x0's value
-- (4 > root₁(x0) = 0 ⇒ ¬(x0 > root₁(x0)) as a linear GT literal)
#guard Explain.run' (do
  Solver.init
  let c4 ← liftS (liftC (CellStore.fresh (.rat 4 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c4 })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let r ← project #[MPoly.sub (MPoly.mul x1 x1) x0] 1
  let st ← get
  let s ← liftS get
  return r == some ()
    && st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.gt, [(x0, false)]⟩))

/-! ## the simplify cluster (12d.5) -/

-- simplifyWithEq: rewrite by x1−x0, result drops below max with value
-- false ⇒ emitted + replaced by true (dropped from the core)
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2), false)]⟩)
  let (out, modified) ← simplifyWithEq #[⟨b, false⟩] (MPoly.sub x1 x0) 1
  let st ← get
  let s ← liftS get
  return modified && out == #[]
    && st.result == #[⟨2, false⟩]
    && s.atoms[2]! == some (.ineq ⟨.gt,
      [(MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 2), false)]⟩))

-- same rewrite with value true ⇒ the ORIGINAL literal is kept
#guard Explain.run' (do
  Solver.init
  let c2 ← liftS (liftC (CellStore.fresh (.rat 2 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c2 })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let b ← liftS (mkIneqAtom ⟨.gt, [(MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2), false)]⟩)
  let (out, modified) ← simplifyWithEq #[⟨b, false⟩] (MPoly.sub x1 x0) 1
  return !modified && out == #[⟨b, false⟩] && (← get).result == #[])

-- non-const lc of the equation ⇒ lc diseq assumption (positive EQ
-- literal, add_assumption sign=true)
#guard Explain.run' (do
  Solver.init
  let cm1 ← liftS (liftC (CellStore.fresh (.rat (-1) : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 cm1 })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let b ← liftS (mkIneqAtom ⟨.gt,
    [(MPoly.smulTerm 1 [(1,2)] x0, false)]⟩)
  let (out, _) ← simplifyWithEq #[⟨b, false⟩] (MPoly.sub (MPoly.mul x0 x1) oneM) 1
  let st ← get
  let s ← liftS get
  return out == #[]
    && st.result == #[⟨2, false⟩, ⟨3, false⟩]
    && s.atoms[2]! == some (.ineq ⟨.gt, [(x0, false)]⟩)
    && s.atoms[3]! == some (.ineq ⟨.eq, [(x0, false)]⟩))

-- select_eq: minimal degree in max, degree-1 early break
#guard Explain.run' (do
  Solver.init
  let b1 ← liftS (mkIneqAtom ⟨.gt, [(x1, false)]⟩)
  let b2 ← liftS (mkIneqAtom ⟨.eq, [(MPoly.sub (MPoly.mul x1 x1) oneM, false)]⟩)
  let b3 ← liftS (mkIneqAtom ⟨.eq, [(MPoly.sub x1 x0, false)]⟩)
  let r ← selectEq #[⟨b1, false⟩, ⟨b2, false⟩, ⟨b3, false⟩] 1
  return r == some (MPoly.sub x1 x0))

-- simplifyCore: the eq rewrites the gt literal away (true via value
-- false below max); the eq literal itself stays
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let b1 ← liftS (mkIneqAtom ⟨.eq, [(MPoly.sub x1 x0, false)]⟩)
  let b2 ← liftS (mkIneqAtom ⟨.gt, [(MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2), false)]⟩)
  let out ← simplifyCore #[⟨b1, false⟩, ⟨b2, false⟩] 1
  let st ← get
  let s ← liftS get
  return out == #[⟨b1, false⟩]
    && st.result == #[⟨3, false⟩]
    && s.atoms[3]! == some (.ineq ⟨.gt,
      [(MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 2), false)]⟩))

-- select_lower_stage_eq + the lower-stage loop: x2eq equation on x0
-- rewrites the core factor, equation emitted as a negated literal
#guard Explain.run' (do
  Solver.init
  let b1 ← liftS (mkIneqAtom ⟨.eq, [(MPoly.sub x0 (MPoly.ofInt 2), false)]⟩)
  let _ ← liftS (mkVar false)
  let _ ← liftS (mkVar false)
  liftS (modify fun s => { s with var2eq := s.var2eq.set! 0 (some b1) })
  let c5 ← liftS (liftC (CellStore.fresh (.rat 5 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c5 })
  let b2 ← liftS (mkIneqAtom ⟨.gt, [(MPoly.mul x0 x1, false)]⟩)
  let out ← simplifyCore #[⟨b2, false⟩] 1
  let st ← get
  let s ← liftS get
  return out == #[⟨3, false⟩]
    && st.result == #[⟨1, true⟩]
    && s.atoms[3]! == some (.ineq ⟨.gt, [(MPoly.smulTerm 2 [] x1, false)]⟩))

end LeanNonlinearArith.Nlsat.Tests
