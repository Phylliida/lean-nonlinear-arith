import LeanNonlinearArith.Kernel.Roots

/-!
# nla-09 computational-half tests

Isolation and Tarski-query sign determination on hand-checkable algebraic
numbers (√2 and friends), including the `TaQ = 0` case at a rational root
and multiplicity-blindness via the internal square-free pass.
-/

namespace LeanNonlinearArith.Kernel.QPoly.RootsTests

open LeanNonlinearArith.Kernel.QPoly

private def p (cs : Array Rat) : QPoly := trim cs

private def x2m2 : QPoly := p #[-2, 0, 1]          -- x² - 2

-- ## isolation
#guard (isolateRoots x2m2).size == 2
#guard (isolateRoots (p #[1, 0, 1])).size == 0     -- x² + 1: no real roots
#guard (isolateRoots (p #[0, -1, 0, 1])).size == 3 -- x³ - x
-- multiplicities are invisible: (x-1)²(x+2) has two distinct roots
#guard (isolateRoots (mul (mul (p #[-1, 1]) (p #[-1, 1])) (p #[2, 1]))).size == 2
-- each interval isolates exactly one root, endpoints non-root, sorted
#guard Id.run do
  let ivs := isolateRoots (p #[0, -1, 0, 1])
  let q := p #[0, -1, 0, 1]
  let mut ok := ivs.size == 3
  for (a, b) in ivs do
    ok := ok && a < b && eval q a != 0 && eval q b != 0
      && countRootsBetween q a b == 1
  for i in [1:ivs.size] do
    ok := ok && ivs[i-1]!.2 ≤ ivs[i]!.1 + 1  -- sorted (loose: lo increasing)
    ok := ok && ivs[i-1]!.1 < ivs[i]!.1
  return ok

-- ## sign determination at √2 (the positive root of x²-2)
#guard Id.run do
  let ivs := isolateRoots x2m2
  let (a, b) := ivs[1]!                             -- the positive root
  return signAtRoot (p #[-1, 1]) x2m2 a b == 1      -- √2 - 1 > 0
      && signAtRoot (p #[-2, 1]) x2m2 a b == -1     -- √2 - 2 < 0
      && signAtRoot (p #[0, 1]) x2m2 a b == 1       -- √2 > 0
      && signAtRoot x2m2 x2m2 a b == 0              -- p(α) = 0
-- TaQ = 0 at a rational root: sign of (x-1) at the root 1 of (x-1)²(x+2)
#guard Id.run do
  let f := mul (mul (p #[-1, 1]) (p #[-1, 1])) (p #[2, 1])
  let ivs := isolateRoots f
  let (a, b) := ivs[1]!                             -- root 1 (right of -2)
  return signAtRoot (p #[-1, 1]) f a b == 0
      && signAtRoot (p #[1, 1]) f a b == 1          -- 1 + 1 > 0

-- ## refinement: pin √2 to width ≤ (b-a)/2²⁰ and against 1.414 < √2 < 1.415
#guard Id.run do
  let ivs := isolateRoots x2m2
  let (a0, b0) := ivs[1]!
  let (a, b) := refineInterval x2m2 a0 b0 20
  return a < b && countRootsBetween x2m2 a b == 1
      && (b - a) * 1048576 ≤ (b0 - a0) + 1
      && a > 707/500 && b < 283/200                 -- 1.414 < √2 < 1.415

-- ## convertQ2BqInterval (nla-29.1b)
-- both endpoints already dyadic (integers): returned verbatim
#guard convertQ2BqInterval x2m2 1 2
  == .inr (Mpbq.ofInt 1, Mpbq.ofInt 2)
-- non-dyadic lower endpoint 4/3: walk tightens to c = 11/8, d = 3/2
-- (hand-traced against the z3 walk: upper 2 → 3/2, sign + ≠ signA →
-- found_d; 5/4 → 11/8, sign − = signA → c)
#guard convertQ2BqInterval x2m2 (4/3) 2
  == .inr (Mpbq.mk 11 3, Mpbq.mk 3 1)
-- non-dyadic endpoints on both sides (7/5 < √2 < 10/7): c = 721/512,
-- d = 91/64 (hand-traced)
#guard convertQ2BqInterval x2m2 (7/5) (10/7)
  == .inr (Mpbq.mk 721 9, Mpbq.mk 91 6)
-- root hit during the walk: p = (x−3/8)(x−5), a = 1/3 non-dyadic; the
-- first refine lands upper = 3/8 which IS the root → .inl (3/8)
#guard convertQ2BqInterval (p #[15/8, -43/8, 1]) (1/3) (1/2)
  == .inl (Mpbq.mk 3 3)
-- validity shape on a specimen grid: .inr brackets lie inside (a,b)
-- with opposite endpoint signs straddling the root
#guard Id.run do
  let specimens : Array (QPoly × Rat × Rat) :=
    #[(x2m2, 1, 2), (x2m2, 4/3, 3/2), (x2m2, 7/5, 10/7),
      (p #[0, -1, 0, 1], 1/3, 5/4), (p #[-6, 11, -6, 1], 3/2, 5/2)]
  let mut ok := true
  for (q, a, b) in specimens do
    match convertQ2BqInterval q a b with
    | .inl r => ok := ok && eval q r.toRat == 0 && a < r.toRat && r.toRat < b
    | .inr (c, d) =>
      ok := ok && a ≤ c.toRat && c.toRat < d.toRat && d.toRat ≤ b
        && evalSignAtD q c * evalSignAtD q d == -1
  return ok

end LeanNonlinearArith.Kernel.QPoly.RootsTests
