import LeanNonlinearArith.Kernel.ZPoly

/-!
# nla-27 slice-1 tests — Zp/ZPoly behavior pins

`#guard` (native evaluation) — untrusted kernel behavior, pinned against
hand-checked polynomial arithmetic.
-/

namespace LeanNonlinearArith.Kernel.ZPolyTests

open LeanNonlinearArith.Kernel

/-! ## Zp basics -/

-- inverse mod prime: 5·3 = 15 ≡ 1 (mod 7)
#guard (⟨7⟩ : ZpCtx).mul 5 ((⟨7⟩ : ZpCtx).inv 5) == 1
-- inverse mod prime power: 3·9 = 27 ≡ 1 (mod 13)? no — 27 % 13 = 1? 27-26=1 yes
#guard (⟨169⟩ : ZpCtx).mul 3 ((⟨169⟩ : ZpCtx).inv 3) == 1

-- division mod 7: (x² − 1) / (x + 1) = x − 1 (balanced representatives)
#guard (⟨7⟩ : ZpCtx).pdivRem #[-1, 0, 1] #[1, 1] == (#[-1, 1], #[])
-- gcd mod 7 of (x²−1)(x+2) and (x²−1)(x−3) is x²−1 (monic, balanced)
#guard (⟨7⟩ : ZpCtx).pgcd #[-2, -1, 2, 1] #[3, -1, -3, 1] == #[-1, 0, 1]
-- ext gcd: U·(x+1) + V·(x−1) = 1 over GF(7)
#guard
  let (u, v, d) := (⟨7⟩ : ZpCtx).pextGcd #[1, 1] #[-1, 1]
  d == #[1] && (⟨7⟩ : ZpCtx).padd ((⟨7⟩ : ZpCtx).pmul u #[1, 1])
    ((⟨7⟩ : ZpCtx).pmul v #[-1, 1]) == #[1]
-- square-free tests mod 7
#guard (⟨7⟩ : ZpCtx).pisSquareFree #[-1, 0, 1]          -- x²−1: yes
#guard !((⟨7⟩ : ZpCtx).pisSquareFree #[1, 2, 1])        -- (x+1)²: no

/-! ## ZPoly basics -/

-- (x²−1)(x+2) = x³ + 2x² − x − 2
#guard ZPoly.mul #[-1, 0, 1] #[2, 1] == #[-2, -1, 2, 1]
-- exact division back
#guard ZPoly.exactDiv #[-2, -1, 2, 1] #[2, 1] == some #[-1, 0, 1]
-- failed division: (x³+1)/(x+2) not exact
#guard ZPoly.exactDiv #[1, 0, 0, 1] #[2, 1] == none
-- divides
#guard ZPoly.dvd #[-2, -1, 2, 1] #[-1, 0, 1]
#guard !ZPoly.dvd #[1, 0, 0, 1] #[2, 1]
-- content / primitive part: 4x² + 8x + 4 → content 4, pp x² + 2x + 1
#guard ZPoly.getPrimitiveAndContent #[4, 8, 4] == (#[1, 2, 1], 4)
-- pseudo-remainder: prem(x³ + 2x² − x − 2, 2x − 4) — lc-scaled steps:
-- 2A → 8x²−2x−4 → 28x−8 → 96, i.e. 2³·A = Q·(2x−4) + 96
#guard ZPoly.prem #[-2, -1, 2, 1] #[-4, 2] == #[96]

/-! ## mod_gcd (z3's default ℤ gcd) -/

-- gcd((x²−1)(x+2), (x²−1)(x−3)) = x²−1
#guard ZPoly.gcd #[-2, -1, 2, 1] #[3, -1, -3, 1] == #[-1, 0, 1]
-- coprime: gcd(x²+1, x+1) = 1
#guard ZPoly.gcd #[1, 0, 1] #[1, 1] == #[1]
-- content interplay: gcd(2x²−2, 4x−4) = 2x−2
#guard ZPoly.gcd #[-2, 0, 2] #[-4, 4] == #[-2, 2]
-- non-monic result with positive lc: gcd(2x²+x−3, 4x²+4x−3)?
-- 2x²+x−3 = (2x+3)(x−1), 4x²+4x−3 = (2x+3)(2x−1) ⇒ gcd = 2x+3
#guard ZPoly.gcd #[-3, 1, 2] #[-3, 4, 4] == #[3, 2]
-- zero-input cases (flip only when the LC is negative)
#guard ZPoly.gcd #[] #[-3, 2] == #[-3, 2]
#guard ZPoly.gcd #[] #[3, -2] == #[-3, 2]
#guard ZPoly.gcd #[3, -2] #[] == #[-3, 2]

end LeanNonlinearArith.Kernel.ZPolyTests
