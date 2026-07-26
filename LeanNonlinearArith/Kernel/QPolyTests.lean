import LeanNonlinearArith.Kernel.QPoly

/-!
# nla-08 kernel tests — known-value `#guard`s

Hand-checked specimens for every kernel entry point. The psc values are
checked against the classical identities (resultant = `lc(g)^m · ∏ f(βᵢ)`,
discriminant relations) so a convention slip in `pscMatrix` shows up as a
wrong *number*, not a wrong sign somewhere downstream.
-/

namespace LeanNonlinearArith.Kernel.QPoly.Tests

open LeanNonlinearArith.Kernel.QPoly

-- little constructors: p #[a₀, a₁, …]
private def p (cs : Array Rat) : QPoly := trim cs

-- ## arithmetic
#guard add (p #[1, 2]) (p #[3, -2]) == p #[4]          -- (1+2x)+(3-2x) = 4
#guard mul (p #[-1, 1]) (p #[1, 1]) == p #[-1, 0, 1]   -- (x-1)(x+1) = x²-1
#guard (divRem (p #[-1, 0, 1]) (p #[-1, 1])) == (p #[1, 1], zero)
#guard (divRem (p #[1, 0, 1]) (p #[-1, 1])).2 == p #[2]  -- x²+1 = (x+1)(x-1)+2
#guard derivative (p #[5, 3, 0, 2]) == p #[3, 0, 6]
#guard eval (p #[1, -2, 1]) 3 == 4                     -- (x-1)² at 3
#guard eval (p #[1, -2, 1]) 1 == 0

-- ## gcd / square-free
-- gcd(x²-1, x²-2x+1) = x-1 (monic)
#guard gcd (p #[-1, 0, 1]) (p #[1, -2, 1]) == p #[-1, 1]
-- gcd of coprime = 1
#guard gcd (p #[-1, 1]) (p #[1, 1]) == p #[1]
-- squarefree part of (x-1)²(x+2) = (x-1)(x+2) = x²+x-2 (monic)
#guard squarefreePart (mul (mul (p #[-1, 1]) (p #[-1, 1])) (p #[2, 1]))
  == p #[-2, 1, 1]
-- Yun on (x-1)(x+2)² : a₁ = x-1, a₂ = x+2
#guard yun (mul (p #[-1, 1]) (mul (p #[2, 1]) (p #[2, 1])))
  == #[p #[-1, 1], p #[2, 1]]
-- Yun on a square-free cubic: single block, (x-1)(x+1)(x-2) = x³-2x²-x+2
#guard yun (mul (p #[-1, 1]) (mul (p #[1, 1]) (p #[-2, 1])))
  == #[p #[2, -1, -2, 1]]
-- Yun at multiplicity ≥ 3 (2026-07-26 review): (x-1)³ → [1, 1, x-1]
-- (index = multiplicity, filler blocks are the constant 1)
#guard yun (mul (p #[-1, 1]) (mul (p #[-1, 1]) (p #[-1, 1])))
  == #[p #[1], p #[1], p #[-1, 1]]
-- mixed multiplicities: (x-1)(x+2)³ → [x-1, 1, x+2]
#guard yun (mul (p #[-1, 1]) (mul (p #[2, 1]) (mul (p #[2, 1]) (p #[2, 1]))))
  == #[p #[-1, 1], p #[1], p #[2, 1]]
-- reconstruction check: ∏ aᵢ^i rebuilds the (monic) input
#guard Id.run do
  let q := mul (mul (p #[-1, 1]) (p #[-1, 1])) (mul (p #[2, 1]) (p #[3, 2]))
  let blocks := yun q
  let mut acc : QPoly := #[1]
  for i in [0:blocks.size] do
    for _ in [0:i+1] do
      acc := mul acc blocks[i]!
  return acc == monic q

-- ## psc / resultant / discriminant
-- res(x²-1, x²-4) = lc^2·f(2)·f(-2) = 3·3 = 9
#guard resultant (p #[-1, 0, 1]) (p #[-4, 0, 1]) == 9
-- res(x-2, x-3): 1×… size-2 Sylvester: det [[1,-2],[1,-3]] = -1 (= f(3) with
-- the spec's row order); the sign is fixed by the convention — pin it
#guard resultant (p #[-2, 1]) (p #[-3, 1]) == -1
-- shared root ⟹ resultant 0
#guard resultant (p #[-1, 0, 1]) (p #[-1, 1]) == 0
-- discriminant chain of (x-1)²: psc₀ = res(p,p') = 0 (double root), psc₁ = lc(p') = 2
#guard discChain (p #[1, -2, 1]) == #[0, 2]
-- x²-2 (simple roots): res(x²-2, 2x) = lc(g)²·∏(αᵢ-βⱼ) = 4·(√2·(-√2)) = -8;
-- spec matrix det [[1,0,-2],[2,0,0],[0,2,0]] = -8 ✓ both routes agree
#guard resultant (p #[-2, 0, 1]) (p #[0, 2]) == -8
-- resultant chain (x²-1 vs x²-4): psc₁ has the size-2 matrix [[f row][g row]]
#guard (resChain (p #[-1, 0, 1]) (p #[-4, 0, 1])).size == 2

-- ## Sturm
#guard countRealRoots (p #[-2, 0, 1]) == 2              -- x²-2
#guard countRealRoots (p #[1, 0, 1]) == 0               -- x²+1
#guard countRealRoots (p #[0, -1, 0, 1]) == 3           -- x³-x
#guard countRootsBetween (p #[-2, 0, 1]) 0 2 == 1       -- √2 ∈ (0,2]
#guard countRootsBetween (p #[-2, 0, 1]) (-2) 2 == 2
#guard countRootsBetween (p #[0, -1, 0, 1]) (-1/2) (1/2) == 1  -- just 0
-- multiple roots count once: (x-1)² has one distinct root
#guard countRealRoots (p #[1, -2, 1]) == 1
-- root bound: x²-2 → 1 + 2 = 3
#guard rootBound (p #[-2, 0, 1]) == 3

end LeanNonlinearArith.Kernel.QPoly.Tests
