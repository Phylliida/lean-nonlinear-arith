import LeanNonlinearArith.Nlsat.EvaluatorTable

/-!
# nla-12b-ii tests — evaluator assembly pins

`#guard` (native evaluation) — untrusted search behavior, pinned against
hand-checked algebraic facts. Conventions: var 0 = x, var 1 = y.
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
#guard (evalSignAt x2m2 (σ := #[(0, .rat (3/2))])).1 == 1
#guard (evalSignAt x2m2 (σ := #[(0, .rat 1)])).1 == -1
-- interval pass: √2 − 1 > 0 (and the refinement persists, nla-28)
#guard
  let (s, σ') := evalSignAt (MPoly.sub x0 (MPoly.ofInt 1)) #[(0, sqrt2)]
  s == 1 && (match σ'.get? 0 with
    | some (.root _ a b _) => b.toRat - a.toRat < 1
    | _ => false)
-- exact zero via the resultant test: x²−2 at the √2 cell
#guard (evalSignAt x2m2 #[(0, sqrt2)]).1 == 0
-- nonzero through the same machinery: x²−3 at √2
#guard (evalSignAt (MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 3)) #[(0, sqrt2)]).1 == -1
-- bivariate: x·y − 1 at √2,√2
#guard (evalSignAt (MPoly.sub (MPoly.mul x0 x1) (MPoly.ofInt 1))
  #[(0, sqrt2), (1, sqrt2)]).1 == 1
-- sample default (ext2_var2num): sign of y − x² with y unassigned, x ↦ √2,
-- sample 1: 1 − 2 < 0
#guard (evalSignAt (MPoly.sub x1 (MPoly.mul x0 x0)) #[(0, sqrt2)] (some 1)).1 == -1

/-! ## isolateRootsAt -/

-- univariate shortcut
#guard
  let (roots?, _) := isolateRootsAt x2m2 #[]
  match roots? with
  | some rs => rs.size == 2
  | none => false
-- rational fragment: x² − y at y ↦ 2 isolates ±√2
#guard
  let (roots?, _) := isolateRootsAt x2my #[(1, .rat 2)]
  match roots? with
  | some rs =>
    rs.size == 2 && (RAlg.compare rs[0]! sqrt2m).1 == .eq
      && (RAlg.compare rs[1]! sqrt2).1 == .eq
  | none => false
-- algebraic assignment: x² − y at y ↦ √2 ⇒ ±2^{1/4} (resultant x⁴−2, both
-- candidates pass the filter)
#guard
  let (roots?, _) := isolateRootsAt x2my #[(1, sqrt2)]
  match roots? with
  | some rs =>
    rs.size == 2
      && (evalSignAt (MPoly.sub (MPoly.mul (MPoly.mul x0 x0) (MPoly.mul x0 x0))
            (MPoly.ofInt 2)) #[(0, rs[1]!)]).1 == 0
  | none => false
-- the vanished-target case: univariate after substitution, target var
-- already assigned ⇒ no roots
#guard
  let (roots?, _) := isolateRootsAt (MPoly.sub x0 x1) #[(0, .rat 1), (1, .rat 1)]
  roots? == some #[]
-- q ≡ 0 fallback ⇒ none (nla-29): p = x·(y²−2) shares the cell's defining
-- polynomial with the assignment y ↦ √2
#guard
  let (roots?, _) := isolateRootsAt (MPoly.mul x0 (MPoly.sub (MPoly.mul x1 x1)
    (MPoly.ofInt 2))) #[(1, sqrt2)]
  roots? == none

/-! ## isolateRootsSigns -/

-- x²−2: roots ±√2, signs + − + (sample points land between the roots)
#guard
  let (rs?, _) := isolateRootsSigns x2m2 #[]
  match rs? with
  | some (roots, signs) => roots.size == 2 && signs == #[1, -1, 1]
  | none => false
-- x²+1: no roots, single positive sign
#guard
  let (rs?, _) := isolateRootsSigns (MPoly.add (MPoly.mul x0 x0) (MPoly.ofInt 1)) #[]
  rs? == some (#[], #[1])

/-! ## SignTable + infeasible intervals -/

private def ltAtom : IneqAtom := ⟨.lt, [(x2m2, false)]⟩

-- x²−2 < 0: infeasible on (−∞, −√2] ∪ [√2, ∞)
#guard
  let (s?, _) := infeasibleIntervalsIneq ltAtom 0 false #[]
  match s? with
  | some (some d) =>
    d.intervals.size == 2
      && !d.intervals[0]!.lowerInf == false  -- first is (−∞, −√2]
      && d.intervals[0]!.lowerInf
      && !d.intervals[0]!.upperOpen
      && (RAlg.compare d.intervals[0]!.upper sqrt2m).1 == .eq
      && !d.intervals[1]!.lowerOpen
      && (RAlg.compare d.intervals[1]!.lower sqrt2).1 == .eq
      && d.intervals[1]!.upperInf
  | _ => false

-- x²−2 ≤ 0 (negated, i.e. the >-side is infeasible... check ¬(x²−2<0) flip):
-- atom x²−2 < 0 under neg=true: infeasible where it HOLDS: (−√2, √2)
#guard
  let (s?, _) := infeasibleIntervalsIneq ltAtom 0 true #[]
  match s? with
  | some (some d) =>
    d.intervals.size == 1
      && d.intervals[0]!.lowerOpen && d.intervals[0]!.upperOpen
      && (RAlg.compare d.intervals[0]!.lower sqrt2m).1 == .eq
      && (RAlg.compare d.intervals[0]!.upper sqrt2).1 == .eq
  | _ => false

-- root atom: x = root₁(x²−2) (= −√2); infeasible where FALSE (neg=false):
-- (−∞, r₁) ∪ (r₁, ∞), open at the root
#guard
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  let (s?, _) := infeasibleIntervalsRoot ra 0 false #[]
  match s? with
  | some (some d) =>
    d.intervals.size == 2
      && d.intervals[0]!.upperOpen
      && (RAlg.compare d.intervals[0]!.upper sqrt2m).1 == .eq
      && d.intervals[1]!.lowerOpen
      && (RAlg.compare d.intervals[1]!.lower sqrt2m).1 == .eq
  | _ => false
-- same atom negated: the singleton [r₁, r₁]
#guard
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  let (s?, _) := infeasibleIntervalsRoot ra 0 true #[]
  match s? with
  | some (some d) =>
    d.intervals.size == 1
      && !d.intervals[0]!.lowerOpen && !d.intervals[0]!.upperOpen
      && (RAlg.compare d.intervals[0]!.lower sqrt2m).1 == .eq
      && (RAlg.compare d.intervals[0]!.upper sqrt2m).1 == .eq
  | _ => false
-- root index out of range: atom false by definition ⇒ full line infeasible
#guard
  let ra : RootAtom := ⟨.eq, 0, 3, x2m2⟩
  let (s?, _) := infeasibleIntervalsRoot ra 0 false #[]
  match s? with
  | some s => IntervalSet.isFull s
  | none => false

/-! ## eval predicates -/

-- evalIneq: x²−2 < 0 at x ↦ 1 (true), x ↦ 2 (false)
#guard (evalIneq ltAtom false #[(0, .rat 1)]).1 == true
#guard (evalIneq ltAtom false #[(0, .rat 2)]).1 == false
#guard (evalIneq ltAtom true #[(0, .rat 2)]).1 == true
-- evalIneq at an algebraic point: √2² − 2 = 0 is NOT < 0
#guard (evalIneq ltAtom false #[(0, sqrt2)]).1 == false
-- evalRoot: x = root₁(x²−2) at x ↦ −√2 (true), x ↦ √2 (false)
#guard
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  (evalRoot ra false #[(0, sqrt2m)]).1 == some true
#guard
  let ra : RootAtom := ⟨.eq, 0, 1, x2m2⟩
  (evalRoot ra false #[(0, sqrt2)]).1 == some false

end LeanNonlinearArith.Nlsat.EvaluatorTests
