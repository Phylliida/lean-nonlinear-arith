import LeanNonlinearArith.Nlsat.EvaluatorTable

/-!
# nla-12b-ii tests — evaluator assembly pins (cell-store model)

`#guard` (native evaluation) — untrusted search behavior, pinned against
hand-checked algebraic facts. Conventions: var 0 = x, var 1 = y.
Computations run in `CellM` via `CellStore.run'`; assignments are built
from fresh values with `Assignment.ofValues`.
-/

namespace LeanNonlinearArith.Nlsat.EvaluatorTests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.AnumEval

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def sqrt2 : RAlg := .root #[-2, 0, 1] 1 2
private def sqrt2m : RAlg := .root #[-2, 0, 1] (-2) (-1)

private def x2m2 : MPoly := MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 2)
private def x2my : MPoly := MPoly.sub (MPoly.mul x0 x0) x1

/-! ## evalSignAt -/

-- optimistic all-rational pass
#guard CellStore.run' (do
  return (← evalSignAt x2m2 (← Assignment.ofValues [(0, .rat (3/2))])) == 1)
#guard CellStore.run' (do
  return (← evalSignAt x2m2 (← Assignment.ofValues [(0, .rat 1)])) == -1)
-- interval pass: √2 − 1 > 0 (and the refinement persists in the store)
#guard CellStore.run' (do
  let σ ← Assignment.ofValues [(0, sqrt2)]
  let s ← evalSignAt (MPoly.sub x0 (MPoly.ofInt 1)) σ
  match (← CellStore.read (σ.get? 0).get!) with
  | .root _ a b _ => return s == 1 && b.toRat - a.toRat < 1
  | _ => return false)
-- exact zero via the resultant test: x²−2 at the √2 cell
#guard CellStore.run' (do
  return (← evalSignAt x2m2 (← Assignment.ofValues [(0, sqrt2)])) == 0)
-- nonzero through the same machinery: x²−3 at √2
#guard CellStore.run' (do
  return (← evalSignAt (MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 3))
    (← Assignment.ofValues [(0, sqrt2)])) == -1)
-- bivariate: x·y − 1 at √2,√2
#guard CellStore.run' (do
  return (← evalSignAt (MPoly.sub (MPoly.mul x0 x1) (MPoly.ofInt 1))
    (← Assignment.ofValues [(0, sqrt2), (1, sqrt2)])) == 1)
-- sample default (ext2_var2num): sign of y − x² with y unassigned, x ↦ √2,
-- sample 1: 1 − 2 < 0
#guard CellStore.run' (do
  return (← evalSignAt (MPoly.sub x1 (MPoly.mul x0 x0))
    (← Assignment.ofValues [(0, sqrt2)]) (some 1)) == -1)

/-! ## isolateRootsAt -/

-- univariate shortcut
#guard CellStore.run' (do
  return (← isolateRootsAt x2m2 #[]).isSome)
-- rational fragment: x² − y at y ↦ 2 isolates ±√2
#guard CellStore.run' (do
  let σ ← Assignment.ofValues [(1, .rat 2)]
  match (← isolateRootsAt x2my σ) with
  | some rs =>
    if rs.size != 2 then return false
    return (← CellStore.compareC rs[0]! (← CellStore.fresh sqrt2m)) == .eq
      && (← CellStore.compareC rs[1]! (← CellStore.fresh sqrt2)) == .eq
  | none => return false)
-- algebraic assignment: x² − y at y ↦ √2 ⇒ ±2^{1/4} (resultant x⁴−2, both
-- candidates pass the filter)
#guard CellStore.run' (do
  let σ ← Assignment.ofValues [(1, sqrt2)]
  match (← isolateRootsAt x2my σ) with
  | some rs =>
    if rs.size != 2 then return false
    let x4m2 := MPoly.sub (MPoly.mul (MPoly.mul x0 x0) (MPoly.mul x0 x0)) (MPoly.ofInt 2)
    return (← evalSignAt x4m2 (σ.set 0 rs[1]!)) == 0
  | none => return false)
-- the vanished-target case: univariate after substitution, target var
-- already assigned ⇒ no roots
#guard CellStore.run' (do
  let σ ← Assignment.ofValues [(0, .rat 1), (1, .rat 1)]
  return (← isolateRootsAt (MPoly.sub x0 x1) σ) == some #[])
-- q ≡ 0 fallback ⇒ none (nla-29): p = x·(y²−2) shares the cell's defining
-- polynomial with the assignment y ↦ √2
#guard CellStore.run' (do
  let σ ← Assignment.ofValues [(1, sqrt2)]
  let p := MPoly.mul x0 (MPoly.sub (MPoly.mul x1 x1) (MPoly.ofInt 2))
  return (← isolateRootsAt p σ) == none)

/-! ## isolateRootsSigns -/

-- x²−2: roots ±√2, signs + − + (sample points land between the roots)
#guard CellStore.run' (do
  match (← isolateRootsSigns x2m2 #[]) with
  | some (roots, signs) => return roots.size == 2 && signs == #[1, -1, 1]
  | none => return false)
-- x²+1: no roots, single positive sign
#guard CellStore.run' (do
  return (← isolateRootsSigns (MPoly.add (MPoly.mul x0 x0) (MPoly.ofInt 1)) #[])
    == some (#[], #[1]))

/-! ## SignTable + infeasible intervals -/

private def ltAtom : IneqAtom := ⟨.lt, [(x2m2, false)]⟩

-- x²−2 < 0: infeasible on (−∞, −√2] ∪ [√2, ∞)
#guard CellStore.run' (do
  match (← infeasibleIntervalsIneq ltAtom 0 false #[]) with
  | some (some d) =>
    let i0 := d.intervals[0]!
    let i1 := d.intervals[1]!
    return d.intervals.size == 2
      && i0.lowerInf && !i0.upperOpen
      && (← CellStore.compareC i0.upper (← CellStore.fresh sqrt2m)) == .eq
      && !i1.lowerOpen && i1.upperInf
      && (← CellStore.compareC i1.lower (← CellStore.fresh sqrt2)) == .eq
  | _ => return false)

-- atom x²−2 < 0 under neg=true: infeasible where the NEGATION fails,
-- i.e. where x²−2 < 0 holds: (−√2, √2), open both ends
#guard CellStore.run' (do
  match (← infeasibleIntervalsIneq ltAtom 0 true #[]) with
  | some (some d) =>
    let i0 := d.intervals[0]!
    return d.intervals.size == 1
      && i0.lowerOpen && i0.upperOpen
      && (← CellStore.compareC i0.lower (← CellStore.fresh sqrt2m)) == .eq
      && (← CellStore.compareC i0.upper (← CellStore.fresh sqrt2)) == .eq
  | _ => return false)

-- root atom: x = root₁(x²−2) (= −√2); infeasible where FALSE (neg=false):
-- (−∞, r₁) ∪ (r₁, ∞), open at the root
#guard CellStore.run' (do
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  match (← infeasibleIntervalsRoot ra 0 false #[]) with
  | some (some d) =>
    let i0 := d.intervals[0]!
    let i1 := d.intervals[1]!
    return d.intervals.size == 2
      && i0.upperOpen
      && (← CellStore.compareC i0.upper (← CellStore.fresh sqrt2m)) == .eq
      && i1.lowerOpen
      && (← CellStore.compareC i1.lower (← CellStore.fresh sqrt2m)) == .eq
  | _ => return false)
-- same atom negated: the singleton [r₁, r₁]
#guard CellStore.run' (do
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  match (← infeasibleIntervalsRoot ra 0 true #[]) with
  | some (some d) =>
    let i0 := d.intervals[0]!
    return d.intervals.size == 1
      && !i0.lowerOpen && !i0.upperOpen
      && (← CellStore.compareC i0.lower (← CellStore.fresh sqrt2m)) == .eq
      && (← CellStore.compareC i0.upper (← CellStore.fresh sqrt2m)) == .eq
  | _ => return false)
-- root index out of range: atom false by definition ⇒ full line infeasible
#guard CellStore.run' (do
  let ra : RootAtom := ⟨.eq, 0, 3, x2m2⟩
  match (← infeasibleIntervalsRoot ra 0 false #[]) with
  | some s => return IntervalSet.isFull s
  | none => return false)

/-! ## eval predicates -/

-- evalIneq: x²−2 < 0 at x ↦ 1 (true), x ↦ 2 (false), negation flips
#guard CellStore.run' (do
  return (← evalIneq ltAtom false (← Assignment.ofValues [(0, .rat 1)])) == true)
#guard CellStore.run' (do
  return (← evalIneq ltAtom false (← Assignment.ofValues [(0, .rat 2)])) == false)
#guard CellStore.run' (do
  return (← evalIneq ltAtom true (← Assignment.ofValues [(0, .rat 2)])) == true)
-- evalIneq at an algebraic point: √2² − 2 = 0 is NOT < 0
#guard CellStore.run' (do
  return (← evalIneq ltAtom false (← Assignment.ofValues [(0, sqrt2)])) == false)
-- evalRoot: x = root₁(x²−2) at x ↦ −√2 (true), x ↦ √2 (false) — the
-- undef-share regression from the tuple era: the target's value is a
-- store cell, so the erased assignment can no longer lose it
#guard CellStore.run' (do
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  return (← evalRoot ra false (← Assignment.ofValues [(0, sqrt2m)])) == some true)
#guard CellStore.run' (do
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  return (← evalRoot ra false (← Assignment.ofValues [(0, sqrt2)])) == some false)

end LeanNonlinearArith.Nlsat.EvaluatorTests
