import LeanNonlinearArith.Nlsat.IntervalSet

/-!
# nla-12a tests — MPoly core + interval sets

Behavior pins for the untrusted search-side data structures: MPoly
canonical arithmetic, the `mkUnion` case machine (justification-aware
splits, same-justification compression, fullness), and
`pickInComplement`'s deterministic preference order.
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

private def below0closed : IntervalSet :=  -- (-∞, 0]
  mk true true (.rat 0) false false (.rat 0) j0
private def above0closed : IntervalSet :=  -- [0, ∞)
  mk false false (.rat 0) true true (.rat 0) j1
private def below0open : IntervalSet :=    -- (-∞, 0)
  mk true true (.rat 0) true false (.rat 0) j0
private def above0open : IntervalSet :=    -- (0, ∞)
  mk true false (.rat 0) true true (.rat 0) j1

-- (-∞, 0] ∪ [0, ∞) covers ℝ
#guard isFull (mkUnion below0closed above0closed).2.2
-- (-∞, 0) ∪ (0, ∞) misses {0}: not full, and zero is the witness
#guard !isFull (mkUnion below0open above0open).2.2
#guard (pickInComplement (mkUnion below0open above0open).2.2).1 == some (.rat 0)

-- overlap splits keep the earlier interval's justification: [0,2]j0 ∪ [1,3]j1
private def i02 : IntervalSet := mk false false (.rat 0) false false (.rat 2) j0
private def i13 : IntervalSet := mk false false (.rat 1) false false (.rat 3) j1
#guard numIntervals (mkUnion i02 i13).2.2 == 2
#guard (justifications (mkUnion i02 i13).2.2).1 == #[j0, j1]
-- the split point: first interval becomes [0, 1) — its upper is now open
#guard (mkUnion i02 i13).2.2.any fun d =>
  d.intervals[0]!.upperOpen && d.intervals[0]!.upper == .rat 1
    && !d.intervals[1]!.lowerOpen

-- same-justification adjacency merges: [0,1)j0 ∪ [1,2]j0 ⇒ one interval
private def i01 : IntervalSet := mk false false (.rat 0) true false (.rat 1) j0
private def i12 : IntervalSet := mk false false (.rat 1) false false (.rat 2) j0
#guard numIntervals (mkUnion i01 i12).2.2 == 1
-- different justifications stay separate even when adjacent
private def i12' : IntervalSet := mk false false (.rat 1) false false (.rat 2) j1
#guard numIntervals (mkUnion i01 i12').2.2 == 2

-- singleton at a covered left endpoint is consumed: [1,1] ∪ [1,2] ⇒ [1,2]
private def single1 : IntervalSet := mk false false (.rat 1) false false (.rat 1) j0
#guard numIntervals (mkUnion single1 i12).2.2 == 1
#guard (justifications (mkUnion single1 i12).2.2).1 == #[j0]

-- witness preferences: integer above everything
private def uptofive : IntervalSet :=  -- (-∞, 0) ∪ [0, 5/2] under two justs
  (mkUnion below0open (mk false false (.rat 0) false false (.rat (5/2)) j1)).2.2
-- z3 int_gt on a basic value is ⌈v⌉ + 1 (strict even when v is an
-- integer), hence 4 rather than 3 (nla-26.4 faithful pin)
#guard (pickInComplement uptofive).1 == some (.rat 4)

-- integer below everything: [-7/2, ∞) shape
private def fromneg : IntervalSet :=
  (mkUnion (mk false false (.rat (-7/2)) true true (.rat 0) j0) above0open).2.2
-- z3 int_lt on a basic value is ⌊v⌋ − 1: ⌊−7/2⌋ − 1 = −5
#guard (pickInComplement fromneg).1 == some (.rat (-5))

-- rational in a gap (zero excluded by coverage)
private def gapset : IntervalSet :=
  (mkUnion (mk true true (.rat 0) false false (.rat 1) j0)
           (mk false false (.rat 2) true true (.rat 0) j1)).2.2
#guard (pickInComplement gapset).1.any fun w =>
  match w with
  | .rat q => 1 < q && q < 2
  | _ => false

-- irrational shared endpoint: (-∞, √2) ∪ (√2, ∞) ⇒ witness is √2 itself
-- (nla-28: isRational refines the stored cell before the witness is taken,
-- so the witness is a REFINED cell — compare values, not representations)
private def sqrt2punct : IntervalSet :=
  (mkUnion (mk true true (.rat 0) true false sqrt2 j0)
           (mk true false sqrt2 true true (.rat 0) j1)).2.2
#guard !isFull sqrt2punct
#guard match (pickInComplement sqrt2punct).1 with
  | some w => (RAlg.compare w sqrt2).1 == .eq
  | none => false

-- shared endpoint but rational: prefer the rational witness
private def ratpunct : IntervalSet :=
  (mkUnion (mk true true (.rat 0) true false (.rat (1/3)) j0)
           (mk true false (.rat (1/3)) true true (.rat 0) j1)).2.2
#guard (pickInComplement ratpunct).1 == some (.rat (1/3))

-- full set has no witness
#guard (pickInComplement (mkUnion below0closed above0closed).2.2).1 == none

-- empty set: anything goes, zero preferred
#guard (pickInComplement none).1 == some (.rat 0)

/-! ## nla-25.5 — mkUnion differential test

`mkUnion s₁ s₂` must behave as set union pointwise, and every surviving
justification must come from one of the inputs. Probed exhaustively over
a grid of small interval sets (all flag shapes over integer endpoints,
rays, singletons, plus second-generation unions as multi-interval
inputs) against half-integer rational probes that fall on, between, and
outside every endpoint. -/

/-- Rational membership oracle, straight from the interval semantics. -/
private def memb (s : IntervalSet) (q : Rat) : Bool :=
  match s with
  | none => false
  | some d => d.intervals.any fun iv =>
    (iv.lowerInf || (match (RAlg.compare iv.lower (.rat q)).1 with
      | .lt => true | .eq => !iv.lowerOpen | .gt => false)) &&
    (iv.upperInf || (match (RAlg.compare (.rat q) iv.upper).1 with
      | .lt => true | .eq => !iv.upperOpen | .gt => false))

private def probes : List Rat :=
  [-3, -5/2, -2, -3/2, -1, -1/2, 0, 1/3, 1/2, 1, 3/2, 2, 5/2, 3]

private def gridEnds : List Rat := [-2, -1, 0, 1, 2]

/-- Generation 1: every valid single-interval set over the grid. -/
private def gen1 : List IntervalSet := Id.run do
  let mut out : List IntervalSet := []
  let bools := [false, true]
  for a in gridEnds do
    -- singleton [a, a]
    out := mk false false (.rat a) false false (.rat a) j0 :: out
    -- rays
    for o in bools do
      out := mk true true (.rat 0) o false (.rat a) j0 :: out    -- (−∞, a⟩
      out := mk o false (.rat a) true true (.rat 0) j1 :: out    -- ⟨a, ∞)
    -- bounded intervals a < b, all four openness shapes
    for b in gridEnds do
      if a < b then
        for lo in bools do
          for hi in bools do
            out := mk lo false (.rat a) hi false (.rat b) j1 :: out
  return out

/-- Generation 2: some unions (multi-interval inputs for the test). -/
private def gen2 : List IntervalSet :=
  (gen1.take 12).flatMap fun s1 => (gen1.drop 30).take 6 |>.map fun s2 =>
    (mkUnion s1 s2).2.2

/-- Algebraic-endpoint sets (2026-07-26 review: the differential sweep
previously covered rational endpoints only). Probes stay rational — the
oracle exercises the root-vs-rat compare path. -/
private def sqrt3 : RAlg := .root #[-3, 0, 1] 1 2
private def genAlg : List IntervalSet :=
  [mk true false (.rat 0) true false sqrt2 j0,          -- (0, √2)
   mk false false (.rat 1) true false sqrt3 j1,         -- [1, √3)
   mk true false sqrt2 true false sqrt3 j0,             -- (√2, √3)
   mk true true (.rat 0) true false sqrt2 j1,           -- (−∞, √2)
   mk false false sqrt3 true true (.rat 0) j0,          -- [√3, ∞)
   mk true false (.root #[-2, 0, 1] (-2) (-1)) false false sqrt2 j1]  -- (−√2, √2]

private def allSets : List IntervalSet := gen1 ++ gen2 ++ genAlg

#guard allSets.all fun s1 => allSets.all fun s2 =>
  let u := (mkUnion s1 s2).2.2
  probes.all fun q => memb u q == (memb s1 q || memb s2 q)

#guard allSets.all fun s1 => allSets.all fun s2 =>
  let (ls, _) := justifications (mkUnion s1 s2).2.2
  let (l1, _) := justifications s1
  let (l2, _) := justifications s2
  ls.all fun j => l1.contains j || l2.contains j

/-! ## nla-28 — statefulness threading pins -/

-- Acceptance pin 1 (refinement persists): pickInComplement's intGt refines
-- the stored upper endpoint to width < 1/2 (z3 const_cast, :2830) — the
-- returned SET carries the refined cell, not the input-width one
private def uptoSqrt2 : IntervalSet := mk true true (.rat 0) true false sqrt2 j0
#guard (pickInComplement uptoSqrt2).1 == some (.rat 2)
#guard match (pickInComplement uptoSqrt2).2 with
  | some d => match d.intervals[d.intervals.size - 1]!.upper with
    | .root _ a b => b.toRat - a.toRat < 1/2
    | .rat _ => false
  | none => false

-- Acceptance pin 2 (is_rational discovery at a shared endpoint): the root
-- of x²−4 in (1,3) IS 2 — z3's is_rational discovers this (rational-root
-- theorem) and the preference ladder returns the BASIC rational; pre-nla-28
-- this returned the root-represented cell as an "irrational" witness
private def rootRep2 : RAlg := .root #[-4, 0, 1] 1 3
private def ratpunctRoot : IntervalSet :=
  (mkUnion (mk true true (.rat 0) true false rootRep2 j0)
           (mk true false rootRep2 true true (.rat 0) j1)).2.2
#guard (pickInComplement ratpunctRoot).1 == some (.rat 2)
-- …and the discovery persists in the returned set (endpoint became basic)
#guard match (pickInComplement ratpunctRoot).2 with
  | some d => d.intervals[0]!.upper == .rat 2
  | none => false

-- Acceptance pin 3 (mkUnion threads refined inputs): comparing the
-- overlapping √3/√2 cells during the sweep refines BOTH stored endpoints
-- (here exactly one bisection each: (3/2, 2) and (1, 3/2)); the returned
-- input sets carry the refined cells
#guard
  let (s1', s2', _) := mkUnion (mk false false (.rat 0) false false sqrt3 j0)
                               (mk false false (.rat 1) false false sqrt2 j1)
  match s1', s2' with
  | some d1, some d2 =>
    d1.intervals[0]!.upper == .root #[-3, 0, 1] (Mpbq.mk 3 1) 2 &&
    d2.intervals[0]!.upper == .root #[-2, 0, 1] 1 (Mpbq.mk 3 1)
  | _, _ => false

end LeanNonlinearArith.Nlsat.Tests
