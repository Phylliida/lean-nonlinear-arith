import LeanNonlinearArith.Kernel.AnumArith
import LeanNonlinearArith.Kernel.CellStore

/-!
# nla-29.2/29.3 tests — anum arithmetic pins

Value-level checks for the `mkBinary` engine and the field ops:
`signOfPolyAt` against the known defining polynomial of the result
(Tarski query), `.eq` comparisons against independently isolated cells,
rational sandwiches, and the became-basic mid-loop re-dispatch pin
designed so the first Sturm scan cannot isolate (two factors with roots
inside the sum interval) and the first refinement of `a` hits its exact
root.
-/

namespace LeanNonlinearArith.Kernel.RAlg.AnumArithTests

open LeanNonlinearArith.Kernel.QPoly LeanNonlinearArith.Kernel.RAlg
  LeanNonlinearArith.Kernel

private def p (cs : Array Rat) : QPoly := QPoly.trim cs

private def sqrt2 : RAlg := (RAlg.isolateRoots (p #[-2, 0, 1]))[1]!
private def sqrt3 : RAlg := (RAlg.isolateRoots (p #[-3, 0, 1]))[1]!
private def sqrt6 : RAlg := (RAlg.isolateRoots (p #[-6, 0, 1]))[1]!
private def bigRoot : RAlg := (RAlg.isolateRoots (p #[1, 0, -10, 0, 1]))[3]!  -- √2+√3

-- ## zero shortcuts + rat/rat
#guard (add (.rat 0) sqrt2).1 == sqrt2
#guard (mul (.rat 0) sqrt2).1 == .rat 0
#guard (add (.rat (1/2)) (.rat (1/3))).1 == .rat (5/6)
#guard (sub sqrt2 (.rat 0)).1 == sqrt2

-- ## √2 + √3 (mkBinary, add path): root of x⁴−10x²+1, .eq to the
-- independently isolated cell, and operands come back value-equal
#guard Id.run do
  let (c, a', b') := add sqrt2 sqrt3
  return signOfPolyAt (p #[1, 0, -10, 0, 1]) c == 0
    && sign c == 1
    && (compare c bigRoot).1 == .eq
    && (compare a' sqrt2).1 == .eq
    && (compare b' sqrt3).1 == .eq

-- ## √2 · √3 = √6 (mkBinary, mul path)
#guard Id.run do
  let (c, _, _) := mul sqrt2 sqrt3
  return signOfPolyAt (p #[-6, 0, 1]) c == 0
    && (compare c sqrt6).1 == .eq

-- ## √3 − √2 (sub path): the small root 0.318… of x⁴−10x²+1
#guard Id.run do
  let (c, _, _) := sub sqrt3 sqrt2
  return signOfPolyAt (p #[1, 0, -10, 0, 1]) c == 0
    && (compare c (.rat 0)).1 == .gt
    && (compare c (.rat (1/2))).1 == .lt

-- ## neg: −√2 is the isolated negative root
#guard Id.run do
  let nsqrt2 := (RAlg.isolateRoots (p #[-2, 0, 1]))[0]!
  return sign (neg sqrt2) == -1
    && (compare (neg sqrt2) nsqrt2).1 == .eq

-- ## inv: 1/√2 = √2/2, root of 2x²−1, sandwiched 0.707 < · < 0.708
#guard Id.run do
  match inv sqrt2 with
  | some c =>
    return signOfPolyAt (p #[-1, 0, 2]) c == 0
      && (compare c (.rat (707/1000))).1 == .gt
      && (compare c (.rat (708/1000))).1 == .lt
  | none => return false
-- inv of zero is z3's throw ⇒ none (never a silent wrong value)
#guard inv (.rat 0) == none
-- power: 0^0 is z3's throw ⇒ none; (√2)² becomes basic 2
#guard power (.rat 0) 0 == none
#guard power sqrt2 2 == some (.rat 2, sqrt2)

-- ## div: √6/√2 = √3; division by zero ⇒ none (z3's throw)
#guard Id.run do
  match div sqrt6 sqrt2 with
  | some (c, _, _) => return (compare c sqrt3).1 == .eq
  | none => return false
#guard div sqrt2 (.rat 0) == none

-- ## mixed algebraic×basic, NON-dyadic basic (the convert_q2bq_interval
-- fallback): √2 + 1/3 is a root of 9x²−6x−17, ≈ 1.74755
#guard Id.run do
  let (c, _, _) := add sqrt2 (.rat (1/3))
  return signOfPolyAt (p #[-17, -6, 9]) c == 0
    && (compare c (.rat (1747/1000))).1 == .gt
    && (compare c (.rat (437/250))).1 == .lt

-- ## mixed algebraic×basic mul, non-dyadic: √2/3 is a root of 9x²−2
#guard Id.run do
  let (c, _, _) := mul sqrt2 (.rat (1/3))
  return signOfPolyAt (p #[-2, 0, 9]) c == 0

-- ## became-basic mid-mkBinary (the designed pin): a = root of x²−4 in
-- (1,3), b = −√3 in (−32,−1). The sum interval (−31,2) contains roots
-- of BOTH result factors (x²−4x+1 has 0.268; x²+4x+1 has −3.73, −0.268),
-- so the first scan leaves 2 candidates; the first refinement of `a`
-- bisects (1,3) at exactly 2 — became basic. z3 short-circuits the `||`
-- and re-dispatches `add` on (.rat 2, b). Result: 2−√3 ≈ 0.2679, and
-- `a'` is the persisted basic.
#guard Id.run do
  let twoCell := mkRoot (p #[-4, 0, 1]) (Mpbq.ofInt 1) (Mpbq.ofInt 3)
  let negSqrt3 := mkRoot (p #[-3, 0, 1]) (-32) (-1)
  let (c, a', _) := add twoCell negSqrt3
  return a' == .rat 2
    && signOfPolyAt (p #[1, -4, 1]) c == 0
    && (compare c (.rat (27/100))).1 == .lt
    && (compare c (.rat (26/100))).1 == .gt

-- ## CellStore lifts: addC on stored √2/√3, refinements persist in place
#guard Id.run do
  let (c, av, bv) := CellStore.run' do
    let x ← CellStore.fresh sqrt2
    let y ← CellStore.fresh sqrt3
    let z ← CellStore.addC x y
    let c ← CellStore.read z
    let av ← CellStore.read x
    let bv ← CellStore.read y
    return (c, av, bv)
  return signOfPolyAt (p #[1, 0, -10, 0, 1]) c == 0
    && (compare c bigRoot).1 == .eq
    && (compare av sqrt2).1 == .eq
    && (compare bv sqrt3).1 == .eq

-- ## CellStore divC: √6/√2 = √3 through the store
#guard Id.run do
  let r := CellStore.run' (do
    let x ← CellStore.fresh sqrt6
    let y ← CellStore.fresh sqrt2
    match (← CellStore.divC x y) with
    | some z => return some (← CellStore.read z)
    | none => return none)
  match r with
  | some c => return (compare c sqrt3).1 == .eq
  | none => return false

end LeanNonlinearArith.Kernel.RAlg.AnumArithTests
