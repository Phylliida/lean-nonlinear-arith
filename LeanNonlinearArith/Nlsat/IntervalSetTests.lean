import LeanNonlinearArith.Nlsat.IntervalSet

/-!
# nla-12a tests — MPoly core + interval sets (cell-store model)

Behavior pins for the untrusted search-side data structures: MPoly
canonical arithmetic, the `mkUnion` case machine (justification-aware
splits, same-justification compression, fullness), and
`pickInComplement`'s deterministic preference order.

**Store discipline (learned 2026-07-28):** `CellId`s only mean something
inside the store that allocated them — building sets in separate
`CellStore.run'` calls and then mixing them reads out-of-bounds cells
(Lean's panic-returns-default, the F7 lesson). So every pin that mixes
sets runs its whole scenario inside ONE `CellM` computation; the shared
sets live in `buildShared`.
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.IntervalSet

/-! ## MPoly -/

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1

-- (x + y)² evaluated at (3, 5) = 64
#guard (MPoly.mul (MPoly.add x0 x1) (MPoly.add x0 x1)).evalRat
  (fun v => if v == 0 then 3 else 5) == 64

-- x²y + 3x, substitute x := 2 ⇒ 4y + 6; at y = 7 ⇒ 34
private def pxy : MPoly :=
  MPoly.add (MPoly.mul (MPoly.mul x0 x0) x1) (MPoly.smulTerm 3 [] x0)
#guard (pxy.substRat 0 2).evalRat (fun _ => 7) == 34
-- substitution eliminates the variable
#guard (pxy.substRat 0 2).degreeIn 0 == 0

-- x² + 2xy: maxVar, degrees
#guard pxy.maxVar == some 1
#guard pxy.degreeIn 0 == 2
#guard pxy.degreeIn 1 == 1
#guard (MPoly.ofInt 5).maxVar == none
#guard x0.maxVar == some 0

-- univariate bridge: x² − 2 (in var 0) round-trips through QPoly
private def x2m2 : MPoly := MPoly.sub (MPoly.mul x0 x0) (MPoly.ofInt 2)
#guard x2m2.toQPoly? 0 == some #[-2, 0, 1]
#guard (MPoly.ofQPoly #[-2, 0, 1] 0) == x2m2
-- not univariate ⇒ none
#guard pxy.toQPoly? 0 == none

-- canonical arithmetic: p − p = 0, add is commutative on distinct monomials
#guard (MPoly.sub pxy pxy).isZero
#guard MPoly.add x0 x1 == MPoly.add x1 x0

/-! ## Interval sets -/

private def j0 : Literal := ⟨0, false⟩
private def j1 : Literal := ⟨1, false⟩

private def sqrt2 : RAlg := .root #[-2, 0, 1] 1 2
private def sqrt3 : RAlg := .root #[-3, 0, 1] 1 2

/-- The shared test sets, built in ONE store. -/
private structure Shared where
  below0closed : IntervalSet
  above0closed : IntervalSet
  below0open : IntervalSet
  above0open : IntervalSet
  i02 : IntervalSet
  i13 : IntervalSet
  i01 : IntervalSet
  i12 : IntervalSet
  i12' : IntervalSet
  single1 : IntervalSet
  uptoSqrt2 : IntervalSet
  ratpunctRoot : IntervalSet

private def buildShared : CellM Shared := do
  let below0closed ← mk true true (.rat 0) false false (.rat 0) j0
  let above0closed ← mk false false (.rat 0) true true (.rat 0) j1
  let below0open ← mk true true (.rat 0) true false (.rat 0) j0
  let above0open ← mk true false (.rat 0) true true (.rat 0) j1
  let i02 ← mk false false (.rat 0) false false (.rat 2) j0
  let i13 ← mk false false (.rat 1) false false (.rat 3) j1
  let i01 ← mk false false (.rat 0) true false (.rat 1) j0
  let i12 ← mk false false (.rat 1) false false (.rat 2) j0
  let i12' ← mk false false (.rat 1) false false (.rat 2) j1
  let single1 ← mk false false (.rat 1) false false (.rat 1) j0
  let uptoSqrt2 ← mk true true (.rat 0) true false sqrt2 j0
  let ratpunctRoot ← do
    let lo ← mk true true (.rat 0) true false (.root #[-4, 0, 1] 1 3) j0
    let hi ← mk true false (.root #[-4, 0, 1] 1 3) true true (.rat 0) j1
    mkUnion lo hi
  return { below0closed, above0closed, below0open, above0open,
           i02, i13, i01, i12, i12', single1, uptoSqrt2, ratpunctRoot }

private def withShared (f : Shared → CellM α) : α :=
  CellStore.run' (do let s ← buildShared; f s)

-- (-∞, 0] ∪ [0, ∞) covers ℝ
#guard withShared fun s => do
  return isFull (← mkUnion s.below0closed s.above0closed)
-- (-∞, 0) ∪ (0, ∞) misses {0}: not full, and zero is the witness
#guard withShared fun s => do
  let u ← mkUnion s.below0open s.above0open
  if isFull u then return false
  match (← pickInComplement u) with
  | some c => match (← CellStore.read c) with
    | .rat q => return q == 0
    | _ => return false
  | none => return false

-- overlap splits keep the earlier interval's justification: [0,2]j0 ∪ [1,3]j1
#guard withShared fun s => do
  let u ← mkUnion s.i02 s.i13
  return numIntervals u == 2 && (justifications u).1 == #[j0, j1]
-- the split point: first interval becomes [0, 1) — its upper is now open
#guard withShared fun s => do
  let u ← mkUnion s.i02 s.i13
  match u with
  | some d =>
    return d.intervals[0]!.upperOpen
      && (match (← CellStore.read d.intervals[0]!.upper) with
        | .rat q => q == 1 | _ => false)
      && !d.intervals[1]!.lowerOpen
  | none => return false

-- same-justification adjacency merges: [0,1)j0 ∪ [1,2]j0 ⇒ one interval
#guard withShared fun s => do
  return numIntervals (← mkUnion s.i01 s.i12) == 1
-- different justifications stay separate even when adjacent
#guard withShared fun s => do
  return numIntervals (← mkUnion s.i01 s.i12') == 2

-- singleton at a covered left endpoint is consumed: [1,1] ∪ [1,2] ⇒ [1,2]
#guard withShared fun s => do
  let u ← mkUnion s.single1 s.i12
  return numIntervals u == 1 && (justifications u).1 == #[j0]

-- witness preferences: integer above everything
-- (-∞, 0) ∪ [0, 5/2] under two justifications
-- z3 int_gt on a basic value is ⌈v⌉ + 1 (strict even when v is an
-- integer), hence 4 rather than 3 (nla-26.4 faithful pin)
#guard withShared fun s => do
  let hi ← mk false false (.rat 0) false false (.rat (5/2)) j1
  let u ← mkUnion s.below0open hi
  match (← pickInComplement u) with
  | some c => match (← CellStore.read c) with
    | .rat q => return q == 4
    | _ => return false
  | none => return false

-- integer below everything: [-7/2, ∞) shape
-- z3 int_lt on a basic value is ⌊v⌋ − 1: ⌊−7/2⌋ − 1 = −5
#guard withShared fun s => do
  let lo ← mk false false (.rat (-7/2)) true true (.rat 0) j0
  let u ← mkUnion lo s.above0open
  match (← pickInComplement u) with
  | some c => match (← CellStore.read c) with
    | .rat q => return q == -5
    | _ => return false
  | none => return false

-- rational in a gap (zero excluded by coverage)
#guard withShared fun s => do
  let lo ← mk true true (.rat 0) false false (.rat 1) j0
  let hi ← mk false false (.rat 2) true true (.rat 0) j1
  let u ← mkUnion lo hi
  match (← pickInComplement u) with
  | some c => match (← CellStore.read c) with
    | .rat q => return 1 < q && q < 2
    | _ => return false
  | none => return false

-- irrational shared endpoint: (-∞, √2) ∪ (√2, ∞) ⇒ witness is √2 itself
-- (isRational refines the stored cell before the witness is taken, so
-- the witness cell is REFINED — compare values, not representations)
#guard withShared fun s => do
  let lo ← mk true true (.rat 0) true false sqrt2 j0
  let hi ← mk true false sqrt2 true true (.rat 0) j1
  let u ← mkUnion lo hi
  if isFull u then return false
  match (← pickInComplement u) with
  | some c => return (RAlg.compare (← CellStore.read c) sqrt2).1 == .eq
  | none => return false

-- shared endpoint but rational: prefer the rational witness
#guard withShared fun s => do
  let lo ← mk true true (.rat 0) true false (.rat (1/3)) j0
  let hi ← mk true false (.rat (1/3)) true true (.rat 0) j1
  let u ← mkUnion lo hi
  match (← pickInComplement u) with
  | some c => match (← CellStore.read c) with
    | .rat q => return q == 1/3
    | _ => return false
  | none => return false

-- full set has no witness
#guard withShared fun s => do
  let u ← mkUnion s.below0closed s.above0closed
  return (← pickInComplement u) == none

-- empty set: anything goes, zero preferred
#guard CellStore.run' (do
  match (← pickInComplement none) with
  | some c => match (← CellStore.read c) with
    | .rat q => return q == 0
    | _ => return false
  | none => return false)

/-! ## nla-25.5 — mkUnion differential test

`mkUnion s₁ s₂` must behave as set union pointwise, and every surviving
justification must come from one of the inputs. Probed exhaustively over
a grid of small interval sets (all flag shapes over integer endpoints,
rays, singletons, plus second-generation unions as multi-interval
inputs) against half-integer rational probes that fall on, between, and
outside every endpoint. -/

/-- Rational membership oracle, straight from the interval semantics.
Compares against rationals — mutation-free, so no store writes and no
probe allocations (root-vs-rat compare never refines). -/
private def memb (s : IntervalSet) (q : Rat) : CellM Bool := do
  match s with
  | none => return false
  | some d =>
    for iv in d.intervals do
      let lowerOk ←
        if iv.lowerInf then pure true
        else
          match (RAlg.compare (← CellStore.read iv.lower) (.rat q)).1 with
          | .lt => pure true
          | .eq => pure !iv.lowerOpen
          | .gt => pure false
      let upperOk ←
        if iv.upperInf then pure true
        else
          match (RAlg.compare (.rat q) (← CellStore.read iv.upper)).1 with
          | .lt => pure true
          | .eq => pure !iv.upperOpen
          | .gt => pure false
      if lowerOk && upperOk then
        return true
    return false

private def probes : List Rat :=
  [-3, -5/2, -2, -3/2, -1, -1/2, 0, 1/3, 1/2, 1, 3/2, 2, 5/2, 3]

private def gridEnds : List Rat := [-2, -1, 0, 1, 2]

/-- All differential-test sets, built in ONE store. Generation 1: every
valid single-interval set over the grid; generation 2: some unions;
plus algebraic-endpoint sets (2026-07-26 review). -/
private def buildAllSets : CellM (List IntervalSet) := do
  let mut gen1 : List IntervalSet := []
  let bools := [false, true]
  for a in gridEnds do
    gen1 := (← mk false false (.rat a) false false (.rat a) j0) :: gen1
    for o in bools do
      gen1 := (← mk true true (.rat 0) o false (.rat a) j0) :: gen1
      gen1 := (← mk o false (.rat a) true true (.rat 0) j1) :: gen1
    for b in gridEnds do
      if a < b then
        for lo in bools do
          for hi in bools do
            gen1 := (← mk lo false (.rat a) hi false (.rat b) j1) :: gen1
  let mut gen2 : List IntervalSet := []
  for s1 in gen1.take 12 do
    for s2 in (gen1.drop 30).take 6 do
      gen2 := (← mkUnion s1 s2) :: gen2
  let alg : List IntervalSet := [
    (← mk true false (.rat 0) true false sqrt2 j0),
    (← mk false false (.rat 1) true false sqrt3 j1),
    (← mk true false sqrt2 true false sqrt3 j0),
    (← mk true true (.rat 0) true false sqrt2 j1),
    (← mk false false sqrt3 true true (.rat 0) j0),
    (← mk true false (.root #[-2, 0, 1] (-2) (-1)) false false sqrt2 j1)]
  return gen1 ++ gen2 ++ alg

#guard CellStore.run' (do
  let allSets ← buildAllSets
  for s1 in allSets do
    for s2 in allSets do
      let u ← mkUnion s1 s2
      for q in probes do
        let inU ← memb u q
        let in1 ← memb s1 q
        let in2 ← memb s2 q
        if inU != (in1 || in2) then
          return false
  return true)

#guard CellStore.run' (do
  let allSets ← buildAllSets
  for s1 in allSets do
    for s2 in allSets do
      let u ← mkUnion s1 s2
      let (ls, _) := justifications u
      let (l1, _) := justifications s1
      let (l2, _) := justifications s2
      if !ls.all fun j => l1.contains j || l2.contains j then
        return false
  return true)

/-! ## nla-28 — statefulness pins (cell-store model) -/

-- Acceptance pin 1 (refinement persists): pickInComplement's intGt refines
-- the STORED upper endpoint to width < 1/2 (z3 const_cast, :2830) — visible
-- through the set's endpoint id
#guard withShared fun s => do
  match (← pickInComplement s.uptoSqrt2) with
  | some c =>
    match (← CellStore.read c) with
    | .rat q =>
      if q != 2 then return false
      match s.uptoSqrt2 with
      | some d =>
        match (← CellStore.read d.intervals[d.intervals.size - 1]!.upper) with
        | .root _ a b _ => return b.toRat - a.toRat < 1/2
        | _ => return false
      | none => return false
    | _ => return false
  | none => return false

-- Acceptance pin 2 (is_rational discovery at a shared endpoint): the root
-- of x²−4 in (1,3) IS 2 — z3's is_rational discovers this (rational-root
-- theorem) and the preference ladder returns the (now-basic) endpoint cell
#guard withShared fun s => do
  match (← pickInComplement s.ratpunctRoot) with
  | some c => match (← CellStore.read c) with
    | .rat q => return q == 2
    | _ => return false
  | none => return false
-- …and the discovery persists in the shared cell (endpoint became basic)
#guard withShared fun s => do
  let _ ← pickInComplement s.ratpunctRoot
  match s.ratpunctRoot with
  | some d => match (← CellStore.read d.intervals[0]!.upper) with
    | .rat q => return q == 2
    | _ => return false
  | none => return false

-- Acceptance pin 3 (mkUnion refines shared endpoints): comparing the
-- overlapping √3/√2 cells during the sweep refines BOTH stored endpoint
-- cells (here exactly one bisection each: (3/2, 2) and (1, 3/2))
#guard CellStore.run' (do
  let s1 ← mk false false (.rat 0) false false sqrt3 j0
  let s2 ← mk false false (.rat 1) false false sqrt2 j1
  let _ ← mkUnion s1 s2
  match s1, s2 with
  | some d1, some d2 =>
    let u1 ← CellStore.read d1.intervals[0]!.upper
    let u2 ← CellStore.read d2.intervals[0]!.upper
    return u1 == .root #[-3, 0, 1] (Mpbq.mk 3 1) 2
      && u2 == .root #[-2, 0, 1] 1 (Mpbq.mk 3 1)
  | _, _ => return false)

end LeanNonlinearArith.Nlsat.Tests
