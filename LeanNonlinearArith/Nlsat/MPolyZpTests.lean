import LeanNonlinearArith.Nlsat.MPolyZp

/-!
# nla-12d.1b-iii tests — Zp-mode layer pins

`managerNormalize` (both modes), `univEval`/`substitute1`,
`mkGlexMonic`, `lcGlexZpX`, `peekFresh`, Newton interpolation
(differential vs direct evaluation), the linear solver, skeleton +
sparse interpolation round trip, and multivariate CRA (differential
against the nla-27 univariate `ZPoly.craCombineImages` on embedded
univariates + a balancedness/mixed-term case).
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def c (n : Int) : MPoly := MPoly.ofInt n
private def one : MPoly := c 1
private def zp (p : Int) : ZpCtx := ⟨p⟩
private def st (k : Int) (m : Monomial) (p : MPoly) : MPoly := MPoly.smulTerm k m p

/-! ## managerNormalize -/

-- ℤ mode: content strip (gcd of coeffs), identity when primitive
#guard MPoly.managerNormalize none (MPoly.add (st 4 [] x0) (c 6))
    == MPoly.add (st 2 [] x0) (c 3)
#guard MPoly.managerNormalize none (MPoly.add (st 3 [] x0) (c 4))
    == MPoly.add (st 3 [] x0) (c 4)
-- Zp mode: balanced reps, zeros dropped (7 ≡ 0, 8 ≡ 1 mod 7)
#guard MPoly.managerNormalize (some (zp 7)) (MPoly.add (st 8 [] x0) (c 7))
    == x0

/-! ## univEval / substitute1 / mkGlexMonic / lcGlexZpX -/

-- 2x² + 3x + 1 at x = 2 → 15 (ℤ mode)
#guard MPoly.univEval none (MPoly.add (st 2 [] (MPoly.mul x0 x0))
    (MPoly.add (st 3 [] x0) one)) 0 2 == 15
-- same at x = 2 in Z₇ → 15 ≡ 1
#guard MPoly.univEval (some (zp 7)) (MPoly.add (st 2 [] (MPoly.mul x0 x0))
    (MPoly.add (st 3 [] x0) one)) 0 2 == 1

-- substitute x0 := 2 in x0²·x1 + x0 → 4·x1 + 2
#guard MPoly.substitute1 none
    (MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0)) x0) 0 2
  == MPoly.add (st 4 [] x1) (c 2)
-- same in Z₅ → −x1 + 2 (balanced: 4 ≡ −1)
#guard MPoly.substitute1 (some (zp 5))
    (MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0)) x0) 0 2
  == MPoly.add (st (-1) [] x1) (c 2)

-- mk_glex_monic: 2x + 4 in Z₅ → x + 2 (inv 2 = 3: 6≡1, 12≡2)
#guard MPoly.mkGlexMonic (zp 5) (MPoly.add (st 2 [] x0) (c 4))
  == MPoly.add x0 (c 2)

-- lc_glex_ZpX: p = (x1+1)·x0² + 2·x1·x0 + 3, viewed over x0:
-- glex-max stripped monomial is [x1] → lc = x0² + 2·x0
#guard
  let p := MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0))
    (MPoly.add (MPoly.mul x0 x0)
      (MPoly.add (st 2 [(1,1)] x0) (c 3)))
  MPoly.lcGlexZpX p 0
    == MPoly.add (MPoly.mul x0 x0) (st 2 [] x0)

/-! ## peekFresh -/

#guard peekFresh #[] == 0
#guard peekFresh #[0, 1, 2] == 3
#guard peekFresh #[1, 3] == 0

/-! ## Newton interpolation -/

-- interpolate f(x) = x² + 1 over Z₇ from the samples 1, 2, 5 at 0, 1, 2
#guard
  let z := zp 7
  let f := MPoly.add (MPoly.mul x0 x0) one
  let ni := (NewtonInterpolator.reset (c := z))
    |>.add 0 (c 1) |>.add 1 (c 2) |>.add 2 (c 5)  -- 0²+1, 1²+1, 2²+1
  let g := ni.mkPoly 0
  g == f && MPoly.univEval (some z) g 0 3 == 3  -- 10 ≡ 3 mod 7

/-! ## LinearEqSolver -/

-- 2x + y = 1, x + y = 2 over Z₅ → x = −1, y = −2 (balanced: 4, 3)
#guard
  let z := zp 5
  let s : LinearEqSolver z := { n := 2 }
  let s := s.setRow 0 #[2, 1] 1
  let s := s.setRow 1 #[1, 1] 2
  s.solve == some #[-1, -2]

-- singular → none
#guard
  let z := zp 5
  let s : LinearEqSolver z := { n := 2 }
  let s := s.setRow 0 #[1, 1] 1
  let s := s.setRow 1 #[2, 2] 2
  s.solve == none

/-! ## Skeleton + sparse interpolation -/

-- skeleton of (y+1)·x² + 2y·x + 3 over x (x0 = x, x1 = y):
-- entries: stripped [] with powers [0,1,2]... grouped by stripped
-- monomial: [y]→powers {2,1}, [1]→{2,0}
#guard
  let p := MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0))
    (MPoly.add (MPoly.mul x0 x0)
      (MPoly.add (st 2 [(1,1)] x0) (c 3)))
  let sk := Skeleton.build p 0
  sk.entries.size == 2 && sk.maxPowers == 2

-- sparse round trip: rebuild p = x0·x1 + 2·x1 (over x0) from its
-- skeleton with maxPowers samples (samples are x0-free, matching z3's
-- usage where the recursive gcd result lives in the lower vars)
#guard
  let z := zp 7
  let p := MPoly.add (MPoly.mul x0 x1) (st 2 [] x1)
  let sk := Skeleton.build p 0
  let si : SparseInterpolator z sk := {}
  let si := (si.add 0 (st 2 [] x1)).get!     -- p(0) = 2·x1
  let si := (si.add 1 (st 3 [] x1)).get!     -- p(1) = 3·x1
  si.ready && si.mkPoly == some p

-- sparse add rejects a poly whose support escapes the skeleton
#guard
  let z := zp 7
  let p := MPoly.add (MPoly.mul x0 x1) (st 2 [] x1)
  let sk := Skeleton.build p 0
  let si : SparseInterpolator z sk := {}
  (si.add 0 (MPoly.add x0 x1)).isNone

/-! ## craCombineImagesM -/

-- univariate-embedded differential vs nla-27's ZPoly.craCombineImages:
-- C1 = x + 2 (mod 3), C2 = 2x + 1 (mod 5) → same combined poly
#guard
  let toZ (cs : List Int) : ZPoly := cs.toArray
  let (rz, bz) := ZPoly.craCombineImages (toZ [2, 1]) 3 (toZ [1, 2]) 5
  let (rm, bm) := craCombineImagesM (MPoly.add x0 (c 2)) 3
    (MPoly.add (st 2 [] x0) one) 5
  bm == bz && rm == MPoly.add (st (rz[1]!) [] x0) (c (rz[0]!))

-- balanced output: combine x (mod 3) with 1 (mod 5): CRT of (1, 0)
-- coeffs: x: 1·10 + 0·6 = 10 mod 15 → −5; const: 0 + 1·6 = 6
#guard craCombineImagesM x0 3 one 5
    == (MPoly.add (st (-5) [] x0) (c 6), 15)

end LeanNonlinearArith.Nlsat.Tests
