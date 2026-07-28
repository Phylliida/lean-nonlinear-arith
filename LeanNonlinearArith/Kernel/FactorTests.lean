import LeanNonlinearArith.Kernel.Factor

/-!
# nla-27 slice-2 tests — GF(p) factorization pins

`#guard` (native evaluation) — untrusted kernel behavior, pinned against
hand-checked finite-field factorizations.
-/

namespace LeanNonlinearArith.Kernel.FactorTests

open LeanNonlinearArith.Kernel

/-! ## Square-free decomposition over GF(p) -/

-- (x+1)² = x²+2x+1 over GF(7): square-free part (x+1) with multiplicity 2
#guard (zpSquareFreeFactor (⟨7⟩ : ZpCtx) #[1, 2, 1]).factors == #[(#[1, 1], 2)]
-- Frobenius path: x⁷+1 = (x+1)⁷ over GF(7) (derivative vanishes)
#guard (zpSquareFreeFactor (⟨7⟩ : ZpCtx) #[1, 0, 0, 0, 0, 0, 0, 1]).factors
  == #[(#[1, 1], 7)]
-- non-monic input: 3x²−3 = 3(x+1)(x−1) over GF(7): constant carries the lc
#guard
  let fs := zpSquareFreeFactor (⟨7⟩ : ZpCtx) #[-3, 0, 3]
  fs.constant == 3 && fs.factors == #[(#[6, 0, 1], 1)]

/-! ## Berlekamp -/

-- x²−1 = (x+1)(x−1) over GF(7): two linear factors
#guard
  let (ok, fs) := zpFactor (⟨7⟩ : ZpCtx) #[-1, 0, 1]
  ok && fs.distinct == 2 && fs.total == 2
    && fs.reconstruct (⟨7⟩ : ZpCtx) == (⟨7⟩ : ZpCtx).pnorm #[-1, 0, 1]
-- x²+1 is irreducible over GF(7) (7 ≡ 3 mod 4): factored = false
#guard
  let (ok, fs) := zpFactor (⟨7⟩ : ZpCtx) #[1, 0, 1]
  !ok && fs.distinct == 1
-- x³+x+1 is irreducible over GF(2) (no roots, degree 3)
#guard
  let (ok, _) := zpFactor (⟨2⟩ : ZpCtx) #[1, 1, 0, 1]
  !ok
-- x³+x = x(x+1)² over GF(2): square-free decomposition + Berlekamp compose
#guard
  let (ok, fs) := zpFactor (⟨2⟩ : ZpCtx) #[0, 1, 0, 1]
  ok && fs.total == 3
    && fs.reconstruct (⟨2⟩ : ZpCtx) == (⟨2⟩ : ZpCtx).pnorm #[0, 1, 0, 1]
-- x⁴+1 = (x²+2)(x²+3) over GF(5), both quadratics irreducible
#guard
  let (ok, fs) := zpFactor (⟨5⟩ : ZpCtx) #[1, 0, 0, 0, 1]
  ok && fs.distinct == 2
    && fs.reconstruct (⟨5⟩ : ZpCtx) == (⟨5⟩ : ZpCtx).pnorm #[1, 0, 0, 0, 1]
-- x⁷−x splits fully over GF(7) (Fermat): 7 linear factors
#guard
  let (ok, fs) := zpFactor (⟨7⟩ : ZpCtx) #[0, -1, 0, 0, 0, 0, 0, 1]
  ok && fs.distinct == 7
    && fs.reconstruct (⟨7⟩ : ZpCtx) == (⟨7⟩ : ZpCtx).pnorm #[0, -1, 0, 0, 0, 0, 0, 1]
-- every factor found actually divides (differential over small degrees)
#guard (List.range 6).all fun a => (List.range 6).all fun b =>
  let f : Array Int := (⟨7⟩ : ZpCtx).pmul #[(a : Int), 1] #[(b : Int), 0, 1]
  let (_, fs) := zpFactor (⟨7⟩ : ZpCtx) f
  fs.reconstruct (⟨7⟩ : ZpCtx) == (⟨7⟩ : ZpCtx).pnorm f

end LeanNonlinearArith.Kernel.FactorTests
