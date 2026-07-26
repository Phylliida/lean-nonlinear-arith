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

end LeanNonlinearArith.Kernel.QPoly.RootsTests
