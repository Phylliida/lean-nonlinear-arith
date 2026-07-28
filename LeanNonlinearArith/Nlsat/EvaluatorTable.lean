import LeanNonlinearArith.Nlsat.Evaluator

/-!
# nla-12b-ii (part 2) — evaluator: sign tables, atom predicates, infeasible intervals

Port of `nlsat_evaluator.cpp`: the `sign_table` (per-atom root sections
merged across factor polynomials, with per-poly signs on the cells they
cut the line into), the `satisfied`/`eval_ineq`/`eval_root` predicates,
and `infeasible_intervals` (both the ineq-atom cell sweep and the
root-atom case table), with justification literals attached exactly as
the source (`literal(a->bvar(), neg)`).

Parity notes:

* `sign_at` ports the linear-search branch only
  (`LINEAR_SEARCH_THRESHOLD = 8`): the binary-search branch returns
  IDENTICAL values — it is a pure lookup optimization, so this is not
  even a witness-level divergence.
* `get_root(UINT_MAX) = 0` (z3's hack to keep the sweep simple) is an
  `Option Nat` here: `none` plays the sentinel role.
* The `q ≡ 0` fallback inside `isolateRootsAt` (nla-29) propagates as
  `none` — unreachable until the solver feeds a degenerate trace.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-! ## Sign table (`nlsat_evaluator.cpp:37`) -/

/-- z3 `sign_table`: root sections merged across an atom's factor
polynomials. `sections` stores (root, position); `sortedSections` the
section ids in order; `polySections`/`polySigns` the per-poly slices;
`info` = (numRoots, firstSection, firstSign) per polynomial. -/
structure SignTable where
  sections : Array (RAlg × Nat)
  sortedSections : Array Nat
  polySections : Array Nat
  polySigns : Array Int
  info : Array (Nat × Nat × Nat)
deriving Repr, Inhabited

namespace SignTable

def empty : SignTable := ⟨#[], #[], #[], #[], #[]⟩

/-- Merge a polynomial's roots into the section list (z3 `merge` :88):
two-pointer sweep over sorted sections vs new roots; equal values share
a section. nla-28: z3's `m_am.compare` refines the stored section roots
and the new roots in place — threaded back. -/
def merge (t : SignTable) (roots : Array RAlg) : SignTable × Array Nat := Id.run do
  let mut t := t
  let mut roots := roots
  let mut pSectionIds : Array Nat := #[]
  let mut newSorted : Array Nat := #[]
  let mut i1 := 0
  let mut i2 := 0
  let mut j := 0
  while i1 < t.sortedSections.size && i2 < roots.size do
    let s1Id := t.sortedSections[i1]!
    let (s1Root, _) := t.sections[s1Id]!
    let (c, s1Root', r2') := RAlg.compare s1Root roots[i2]!
    t := { t with sections := t.sections.set! s1Id (s1Root', j) }
    roots := roots.set! i2 r2'
    if c == .eq then
      newSorted := newSorted.push s1Id
      pSectionIds := pSectionIds.push s1Id
      i1 := i1 + 1
      i2 := i2 + 1
    else if c == .lt then
      newSorted := newSorted.push s1Id
      i1 := i1 + 1
    else
      let newId := t.sections.size
      t := { t with sections := t.sections.push (roots[i2]!, j) }
      newSorted := newSorted.push newId
      pSectionIds := pSectionIds.push newId
      i2 := i2 + 1
    j := j + 1
  while i1 < t.sortedSections.size do
    let s1Id := t.sortedSections[i1]!
    t := { t with sections := t.sections.set! s1Id (t.sections[s1Id]!.1, j) }
    newSorted := newSorted.push s1Id
    i1 := i1 + 1
    j := j + 1
  while i2 < roots.size do
    let newId := t.sections.size
    t := { t with sections := t.sections.push (roots[i2]!, j) }
    newSorted := newSorted.push newId
    pSectionIds := pSectionIds.push newId
    i2 := i2 + 1
    j := j + 1
  return ({ t with sortedSections := newSorted }, pSectionIds)

/-- z3 `add` (:142): merge roots, append the poly's signs and info. -/
def add (t : SignTable) (roots : Array RAlg) (signs : Array Int) : SignTable := Id.run do
  let mut t := t
  let mut pSectionIds : Array Nat := #[]
  if !roots.isEmpty then
    let (t', ids) := t.merge roots
    t := t'
    pSectionIds := ids
  let firstSign := t.polySigns.size
  let firstSection := t.polySections.size
  return { t with
    polySigns := t.polySigns ++ signs
    polySections := t.polySections ++ pSectionIds
    info := t.info.push (roots.size, firstSection, firstSign) }

/-- z3 `add_const` (:160). -/
def addConst (t : SignTable) (s : Int) : SignTable :=
  { t with
    polySigns := t.polySigns.push s
    info := t.info.push (0, t.polySections.size, t.polySigns.size) }

def numCells (t : SignTable) : Nat := t.sections.size * 2 + 1

/-- z3 `is_section`: odd cell ids are the roots themselves. -/
def isSection (c : Nat) : Bool := c % 2 == 1

/-- z3 `get_root_id` (pre: `is_section c`). -/
def getRootId (t : SignTable) (c : Nat) : Nat :=
  t.sortedSections[c / 2]!

/-- z3 `get_root` — the `none` sentinel returns zero (z3's UINT_MAX hack). -/
def getRoot (t : SignTable) (idx : Option Nat) : RAlg :=
  match idx with
  | none => .rat 0
  | some i => t.sections[i]!.1

/-- Cell id of the poly's `i`-th root (z3 `cell_id`). -/
def cellIdOf (t : SignTable) (pinfo : Nat × Nat × Nat) (i : Nat) : Nat :=
  let (_, firstSection, _) := pinfo
  t.sections[t.polySections[firstSection + i]!]!.2 * 2 + 1

/-- z3 `get_sign`. -/
def getSign (t : SignTable) (pinfo : Nat × Nat × Nat) (i : Nat) : Int :=
  let (_, _, firstSign) := pinfo
  t.polySigns[firstSign + i]!

/-- z3 `sign_at` (:235), linear-search branch (see header parity note). -/
def signAt (t : SignTable) (infoId c : Nat) : Int := Id.run do
  let pinfo := t.info[infoId]!
  let (numRoots, _, _) := pinfo
  for i in [:numRoots] do
    let sectionCellId := t.cellIdOf pinfo i
    if sectionCellId == c then
      return 0
    else if sectionCellId > c then
      return t.getSign pinfo i
  return t.getSign pinfo numRoots

end SignTable

/-! ## Atom predicates -/

/-- z3 `satisfied(sign, kind)` for ineq atoms. -/
def satisfiedIneq (s : Int) : IneqKind → Bool
  | .eq => s == 0
  | .lt => s < 0
  | .gt => s > 0

/-- z3 `satisfied(sign, kind)` for root atoms. -/
def satisfiedRoot (s : Int) : RootKind → Bool
  | .eq => s == 0
  | .lt => s < 0
  | .gt => s > 0
  | .le => s ≤ 0
  | .ge => s ≥ 0

/-- z3 `sign_at(ineq_atom, table, cell)` (:457): product of factor signs,
even-powered factors clamped to positive. -/
def signAtAtom (a : IneqAtom) (t : SignTable) (c : Nat) : Int := Id.run do
  let mut sign : Int := 1
  for i in [:a.factors.length] do
    let (_, isEven) := a.factors[i]!
    let mut curr := t.signAt i c
    if isEven && curr < 0 then
      curr := 1
    sign := sign * curr
    if sign == 0 then
      break
  return sign

/-- z3 `eval_sign` (:386): sign of a fully-assigned polynomial. -/
def evalSign (p : MPoly) (σ : Assignment) : Int × Assignment :=
  AnumEval.evalSignAt p σ

/-- z3 `eval_ineq` (:404). -/
def evalIneq (a : IneqAtom) (neg : Bool) (σ : Assignment) : Bool × Assignment := Id.run do
  let mut σ := σ
  let mut sign : Int := 1
  for (p, isEven) in a.factors do
    let (s, σ') := evalSign p σ
    σ := σ'
    let mut curr := s
    if isEven && curr < 0 then
      curr := 1
    sign := sign * curr
    if sign == 0 then
      break
  let r := satisfiedIneq sign a.kind
  return (if neg then !r else r, σ)

/-- z3 `eval_root` (:427): isolate the roots of `a.p` under the
assignment with `a.x` undefined, compare the assigned value against the
`i`-th root. -/
def evalRoot (a : RootAtom) (neg : Bool) (σ : Assignment) : Option Bool × Assignment := Id.run do
  -- undef_var_assignment SHARES the underlying store in z3: refinements
  -- of the other cells persist; the target's own value is re-attached
  let target := (σ.get? a.x).getD (.rat 0)
  let (roots?, σ') := AnumEval.isolateRootsAt a.p (σ.erase a.x)
  let σ := σ'.set a.x target
  match roots? with
  | none => return (none, σ)   -- nla-29 fallback path
  | some roots =>
    if a.i > roots.size then
      return (some neg, σ)
    let (o, _, _) := RAlg.compare target roots[a.i - 1]!
    let s : Int := match o with | .lt => -1 | .eq => 0 | .gt => 1
    let r := satisfiedRoot s a.kind
    return (some (if neg then !r else r), σ)

/-- z3 `evaluator::add` (:446): add `p`'s row to the table — constant
row when `x` exceeds `p`'s max var, else isolate roots + signs. -/
def addToTable (p : MPoly) (x : Var) (t : SignTable) (σ : Assignment) :
    Option SignTable × Assignment := Id.run do
  match p.maxVar with
  | some mv =>
    if mv < x then
      let (s, σ) := evalSign p σ
      return (some (t.addConst s), σ)
    else
      let (rs?, σ) := AnumEval.isolateRootsSigns p (σ.erase x)
      match rs? with
      | none => return (none, σ)
      | some (roots, signs) => return (some (t.add roots signs), σ)
  | none =>
    let (s, σ) := evalSign p σ
    return (some (t.addConst s), σ)

/-! ## Infeasible intervals (`nlsat_evaluator.cpp:494/599`) -/

/-- z3 `infeasible_intervals(ineq_atom)` (:471): sweep the sign table's
cells, emitting intervals where the atom (under `neg`) FAILS, each
justified by `literal(a.bvar, neg)`. `clauseId` stays a parameter
(the solver supplies it at 12c). -/
def infeasibleIntervalsIneq (a : IneqAtom) (bvar : Nat) (neg : Bool) (σ : Assignment)
    (clauseId : Option Nat := none) : Option IntervalSet × Assignment := Id.run do
  let x := match a.factors.foldl (fun acc (p, _) => max acc p.maxVar) none with
    | some v => v
    | none => 0
  let mut t := SignTable.empty
  let mut σ := σ
  for (p, _) in a.factors do
    let (t?, σ') := addToTable p x t σ
    σ := σ'
    match t? with
    | none => return (none, σ)
    | some t' => t := t'
  let jst : Literal := ⟨bvar, neg⟩
  let dummy : RAlg := .rat 0
  let mut result : IntervalSet := none
  let mut prevSat := true
  let mut prevInf := true
  let mut prevOpen := true
  let mut prevRootId : Option Nat := none
  let numCells := t.numCells
  for c in [:numCells] do
    let sign := signAtAtom a t c
    let sat := satisfiedIneq sign a.kind
    if (if neg then !sat else sat) then
      -- current cell is satisfied
      if !prevSat then
        let (currOpen, currRootId) :=
          if SignTable.isSection c then (true, some (t.getRootId c))
          else (false, some (t.getRootId (c - 1)))
        let set := IntervalSet.mk prevOpen prevInf (t.getRoot prevRootId)
          currOpen false (t.getRoot currRootId) jst clauseId
        result := IntervalSet.mkUnion result set |>.2.2
        prevSat := true
    else
      -- current cell is not satisfied
      if prevSat then
        if c == 0 then
          if numCells == 1 then
            result := IntervalSet.mk true true dummy true true dummy jst clauseId
          else
            prevOpen := true
            prevInf := true
            prevRootId := none
        else
          prevInf := false
          if SignTable.isSection c then
            prevOpen := false
            prevRootId := some (t.getRootId c)
          else
            prevOpen := true
            prevRootId := some (t.getRootId (c - 1))
        prevSat := false
      if c == numCells - 1 then
        let set := IntervalSet.mk prevOpen prevInf (t.getRoot prevRootId)
          true true dummy jst clauseId
        result := IntervalSet.mkUnion result set |>.2.2
  return (some result, σ)

/-- z3 `infeasible_intervals(root_atom)` (:599): the case table over
`ROOT_EQ/LT/GT/LE/GE` (negated: the intervals where the atom FAILS). -/
def infeasibleIntervalsRoot (a : RootAtom) (bvar : Nat) (neg : Bool) (σ : Assignment)
    (clauseId : Option Nat := none) : Option IntervalSet × Assignment := Id.run do
  let jst : Literal := ⟨bvar, neg⟩
  let dummy : RAlg := .rat 0
  let (roots?, σ) := AnumEval.isolateRootsAt a.p (σ.erase a.x)
  match roots? with
  | none => return (none, σ)   -- nla-29 fallback path
  | some roots =>
    if a.i > roots.size then
      -- p does not have sufficient roots: the atom is false by definition
      if neg then
        return (some none, σ)   -- empty set
      else
        return (some (IntervalSet.mk true true dummy true true dummy jst clauseId), σ)
    let ri := roots[a.i - 1]!
    let result : IntervalSet :=
      match a.kind, neg with
      | .eq, true =>
        IntervalSet.mk false false ri false false ri jst clauseId           -- [r_i, r_i]
      | .eq, false =>
        IntervalSet.mkUnion
          (IntervalSet.mk true true dummy true false ri jst clauseId)       -- (-oo, r_i)
          (IntervalSet.mk true false ri true true dummy jst clauseId) |>.2.2 -- (r_i, oo)
      | .lt, true =>
        IntervalSet.mk true true dummy true false ri jst clauseId           -- (-oo, r_i)
      | .lt, false =>
        IntervalSet.mk false false ri true true dummy jst clauseId          -- [r_i, oo)
      | .gt, true =>
        IntervalSet.mk true false ri true true dummy jst clauseId           -- (r_i, oo)
      | .gt, false =>
        IntervalSet.mk true true dummy false false ri jst clauseId          -- (-oo, r_i]
      | .le, true =>
        IntervalSet.mk true true dummy false false ri jst clauseId          -- (-oo, r_i]
      | .le, false =>
        IntervalSet.mk true false ri true true dummy jst clauseId           -- (r_i, oo)
      | .ge, true =>
        IntervalSet.mk false false ri true true dummy jst clauseId          -- [r_i, oo)
      | .ge, false =>
        IntervalSet.mk true true dummy true false ri jst clauseId           -- (-oo, r_i)
    return (some result, σ)

end LeanNonlinearArith.Nlsat
