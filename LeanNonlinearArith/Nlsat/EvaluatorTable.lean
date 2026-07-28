import LeanNonlinearArith.Nlsat.Evaluator

/-!
# nla-12b-ii (part 2) — evaluator: sign tables, atom predicates, infeasible intervals

Port of `nlsat_evaluator.cpp`: the `sign_table` (per-atom root sections
merged across factor polynomials, with per-poly signs on the cells they
cut the line into), the `satisfied`/`eval_ineq`/`eval_root` predicates,
and `infeasible_intervals` (both the ineq-atom cell sweep and the
root-atom case table), with justification literals attached exactly as
the source (`literal(a->bvar(), neg)`).

Cell-store model: sections and interval endpoints are `CellId`s;
endpoint cells are SHARED between the table and the interval sets it
produces (z3's `m_am.set` semantics), so refinements made later by
`pick_in_complement` reach back into the table — the nla-28
statefulness, now structural.

Parity notes:

* `sign_at` ports the linear-search branch only
  (`LINEAR_SEARCH_THRESHOLD = 8`): the binary-search branch returns
  IDENTICAL values — a pure lookup optimization, not even a
  witness-level divergence.
* `get_root(UINT_MAX) = 0` (z3's hack) is an `Option Nat` here; the
  sentinel resolves to a shared dummy cell (its value is never read —
  the `Inf` flags guard it, exactly as z3's unset `anum dummy`).
* The `q ≡ 0` fallback inside `isolateRootsAt` (nla-29) propagates as
  `none` — unreachable until the solver feeds a degenerate trace.
-/

namespace LeanNonlinearArith.Nlsat

open LeanNonlinearArith.Kernel

/-! ## Sign table (`nlsat_evaluator.cpp:37`) -/

/-- z3 `sign_table`: root sections merged across an atom's factor
polynomials. `sections` stores (root cell, position); `sortedSections`
the section ids in order; `polySections`/`polySigns` the per-poly
slices; `info` = (numRoots, firstSection, firstSign) per polynomial. -/
structure SignTable where
  sections : Array (CellId × Nat)
  sortedSections : Array Nat
  polySections : Array Nat
  polySigns : Array Int
  info : Array (Nat × Nat × Nat)
deriving Repr, Inhabited

namespace SignTable

def empty : SignTable := ⟨#[], #[], #[], #[], #[]⟩

/-- Merge a polynomial's roots into the section list (z3 `merge` :88):
two-pointer sweep over sorted sections vs new roots; equal values share
a section. Section cells are shared (z3 `m_am.set`), and compares
refine them in place. -/
def merge (t : SignTable) (roots : Array CellId) : CellM (SignTable × Array Nat) := do
  let mut t := t
  let mut pSectionIds : Array Nat := #[]
  let mut newSorted : Array Nat := #[]
  let mut i1 := 0
  let mut i2 := 0
  let mut j := 0
  while i1 < t.sortedSections.size && i2 < roots.size do
    let s1Id := t.sortedSections[i1]!
    let (s1Root, _) := t.sections[s1Id]!
    let c ← CellStore.compareC s1Root roots[i2]!
    t := { t with sections := t.sections.set! s1Id (s1Root, j) }
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
def add (t : SignTable) (roots : Array CellId) (signs : Array Int) : CellM SignTable := do
  let mut t := t
  let mut pSectionIds : Array Nat := #[]
  if !roots.isEmpty then
    let (t', ids) ← t.merge roots
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

/-- z3 `get_root` — the `none` sentinel resolves to the shared dummy
cell (z3's UINT_MAX hack; the dummy's value is never read). -/
def getRoot (t : SignTable) (idx : Option Nat) (dummy : CellId) : CellId :=
  match idx with
  | none => dummy
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
def evalSign (p : MPoly) (σ : Assignment) : CellM Int :=
  AnumEval.evalSignAt p σ

/-- z3 `eval_ineq` (:404). -/
def evalIneq (a : IneqAtom) (neg : Bool) (σ : Assignment) : CellM Bool := do
  let mut sign : Int := 1
  for (p, isEven) in a.factors do
    let s ← evalSign p σ
    let mut curr := s
    if isEven && curr < 0 then
      curr := 1
    sign := sign * curr
    if sign == 0 then
      break
  let r := satisfiedIneq sign a.kind
  return (if neg then !r else r)

/-- z3 `eval_root` (:427): isolate the roots of `a.p` under the
assignment with `a.x` undefined, compare the assigned value against the
`i`-th root. The undef assignment shares the store — refinements during
isolation persist into `σ`, exactly z3. -/
def evalRoot (a : RootAtom) (neg : Bool) (σ : Assignment) : CellM (Option Bool) := do
  let target := (σ.get? a.x).get!   -- pre: a.x assigned (z3 SASSERT)
  match (← AnumEval.isolateRootsAt a.p (σ.erase a.x)) with
  | none => return none   -- nla-29 fallback path
  | some roots =>
    if a.i > roots.size then
      return some neg
    let o ← CellStore.compareC target roots[a.i - 1]!
    let s : Int := match o with | .lt => -1 | .eq => 0 | .gt => 1
    let r := satisfiedRoot s a.kind
    return some (if neg then !r else r)

/-- z3 `evaluator::add` (:446): add `p`'s row to the table — constant
row when `x` exceeds `p`'s max var, else isolate roots + signs. -/
def addToTable (p : MPoly) (x : Var) (t : SignTable) (σ : Assignment) :
    CellM (Option SignTable) := do
  match p.maxVar with
  | some mv =>
    if mv < x then
      return some (t.addConst (← evalSign p σ))
    else
      match (← AnumEval.isolateRootsSigns p (σ.erase x)) with
      | none => return none
      | some (roots, signs) => return some (← t.add roots signs)
  | none =>
    return some (t.addConst (← evalSign p σ))

/-! ## Infeasible intervals (`nlsat_evaluator.cpp:494/599`) -/

/-- z3 `infeasible_intervals(ineq_atom)` (:471): sweep the sign table's
cells, emitting intervals where the atom (under `neg`) FAILS, each
justified by `literal(a.bvar, neg)`. `clauseId` stays a parameter
(the solver supplies it at 12c). -/
def infeasibleIntervalsIneq (a : IneqAtom) (bvar : Nat) (neg : Bool) (σ : Assignment)
    (clauseId : Option Nat := none) : CellM (Option IntervalSet) := do
  let x := match a.factors.foldl (fun acc (p, _) => max acc p.maxVar) none with
    | some v => v
    | none => 0
  let mut t := SignTable.empty
  for (p, _) in a.factors do
    match (← addToTable p x t σ) with
    | none => return none
    | some t' => t := t'
  let jst : Literal := ⟨bvar, neg⟩
  let dummy ← CellStore.fresh (.rat 0)
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
        let set := IntervalSet.mkIds prevOpen prevInf (t.getRoot prevRootId dummy)
          currOpen false (t.getRoot currRootId dummy) jst clauseId
        result := (← IntervalSet.mkUnion result set)
        prevSat := true
    else
      -- current cell is not satisfied
      if prevSat then
        if c == 0 then
          if numCells == 1 then
            result := IntervalSet.mkIds true true dummy true true dummy jst clauseId
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
        let set := IntervalSet.mkIds prevOpen prevInf (t.getRoot prevRootId dummy)
          true true dummy jst clauseId
        result := (← IntervalSet.mkUnion result set)
  return some result

/-- z3 `infeasible_intervals(root_atom)` (:599): the case table over
`ROOT_EQ/LT/GT/LE/GE` (negated: the intervals where the atom FAILS). -/
def infeasibleIntervalsRoot (a : RootAtom) (bvar : Nat) (neg : Bool) (σ : Assignment)
    (clauseId : Option Nat := none) : CellM (Option IntervalSet) := do
  let jst : Literal := ⟨bvar, neg⟩
  let dummy ← CellStore.fresh (.rat 0)
  match (← AnumEval.isolateRootsAt a.p (σ.erase a.x)) with
  | none => return none   -- nla-29 fallback path
  | some roots =>
    if a.i > roots.size then
      -- p does not have sufficient roots: the atom is false by definition
      if neg then
        return some none   -- empty set
      else
        return some (IntervalSet.mkIds true true dummy true true dummy jst clauseId)
    let ri := roots[a.i - 1]!
    let result : IntervalSet :=
      match a.kind, neg with
      | .eq, true =>
        IntervalSet.mkIds false false ri false false ri jst clauseId           -- [r_i, r_i]
      | .eq, false =>
        IntervalSet.mkIds true true dummy true false ri jst clauseId           -- (-oo, r_i)
      | .lt, true =>
        IntervalSet.mkIds true true dummy true false ri jst clauseId           -- (-oo, r_i)
      | .lt, false =>
        IntervalSet.mkIds false false ri true true dummy jst clauseId          -- [r_i, oo)
      | .gt, true =>
        IntervalSet.mkIds true false ri true true dummy jst clauseId           -- (r_i, oo)
      | .gt, false =>
        IntervalSet.mkIds true true dummy false false ri jst clauseId          -- (-oo, r_i]
      | .le, true =>
        IntervalSet.mkIds true true dummy false false ri jst clauseId          -- (-oo, r_i]
      | .le, false =>
        IntervalSet.mkIds true false ri true true dummy jst clauseId           -- (r_i, oo)
      | .ge, true =>
        IntervalSet.mkIds false false ri true true dummy jst clauseId          -- [r_i, oo)
      | .ge, false =>
        IntervalSet.mkIds true true dummy true false ri jst clauseId           -- (-oo, r_i)
    -- ROOT_EQ unnegated is the union of the two rays
    match a.kind, neg with
    | .eq, false =>
      let s2 := IntervalSet.mkIds true false ri true true dummy jst clauseId  -- (r_i, oo)
      return some (← IntervalSet.mkUnion result s2)
    | _, _ => return some result

end LeanNonlinearArith.Nlsat
