import LeanNonlinearArith.Nlsat.MPolyGcd

/-!
# nla-12d.1b-ii/iv tests — the multivariate gcd cluster pins

`iccpM` (filter/content paths), the `gcdM` ladder (zero/eq/const,
single-var `gcdContentM`, univariate `uniModGcd`, multivariate
`modGcd`), `euclidGcdM` in Zp, `iccpZpXM` (min-degree strip / cheap /
bucket paths), the **constant-image quirk** (`uniModGcd(2x+1, 2x+3)
= 2`, ported verbatim), and the **modular-vs-PRS differential** (z3's
own `mgcd_check`: `modGcd` must agree with `gcdPrsM` on the same
inputs).
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def c (n : Int) : MPoly := MPoly.ofInt n
private def one : MPoly := c 1
private def st (k : Int) (m : Monomial) (p : MPoly) : MPoly := MPoly.smulTerm k m p
private def zp (p : Int) : ZpCtx := ⟨p⟩

/-! ## iccpM -/

-- iccp(2·x0²·x1 + 4·x0·x1, x0) = (2, x1, x0² + 2·x0)
#guard
  let p := MPoly.add (st 2 [(1,1)] (MPoly.mul x0 x0)) (st 4 [(1,1)] x0)
  iccpM none p 0 == (2, x1, MPoly.add (MPoly.mul x0 x0) (st 2 [] x0))

-- pure-x^k quick filter: iccp(x0² + x0·x1, x0) has a pure x0² term ⇒ c = 1
#guard
  let p := MPoly.add (MPoly.mul x0 x0) (MPoly.mul x0 x1)
  iccpM none p 0 == (1, one, p)

-- degree-0 in x: integer content only
#guard iccpM none (MPoly.add (st 4 [] x1) (c 6)) 0
    == (2, one, MPoly.add (st 2 [] x1) (c 3))

/-! ## gcdM ladder: zero / eq / const -/

#guard gcdM none MPoly.zero (MPoly.add x0 one) == MPoly.add x0 one
#guard gcdM none (MPoly.neg (MPoly.add x0 one)) MPoly.zero == MPoly.add x0 one  -- flip
#guard gcdM none (c 6) (st 4 [] x0) == c 2
#guard gcdM none (MPoly.add x0 one) (MPoly.add x0 one) == MPoly.add x0 one

-- var in only one side: gcd(x0·(x1+1), x1+1) = x1+1
#guard gcdM none (MPoly.mul x0 (MPoly.add x1 one)) (MPoly.add x1 one)
    == MPoly.add x1 one

/-! ## uniModGcd (univariate modular) -/

-- gcd(2(x+1)², 2(x+1)) = 2(x+1)
#guard gcdM none (st 2 [] (MPoly.pw (MPoly.add x0 one) 2)) (st 2 [] (MPoly.add x0 one))
    == st 2 [] (MPoly.add x0 one)

-- gcd(x²−1, x²−2x+1) = x−1
#guard
  let a := MPoly.sub (MPoly.mul x0 x0) one
  let b := MPoly.pw (MPoly.sub x0 one) 2
  gcdM none a b == MPoly.sub x0 one

-- QUIRK PIN (ported verbatim): uniModGcd(2x+1, 2x+3) = 2 — the
-- constant modular image branch returns q = lc_g when d_a = 1,
-- although the true gcd is 1 (see MPolyGcd.lean header)
#guard gcdM none (MPoly.add (st 2 [] x0) one) (MPoly.add (st 2 [] x0) (c 3))
    == c 2

/-! ## euclidGcdM (Zp mode) -/

-- gcd(x²−1, (x−1)²) = x−1 over Z₇
#guard
  let a := MPoly.sub (MPoly.mul x0 x0) one
  let b := MPoly.pw (MPoly.sub x0 one) 2
  euclidGcdM (zp 7) a b == MPoly.sub x0 one
#guard euclidGcdM (zp 7) (c 3) (c 5) == one

/-! ## iccpZpXM -/

-- min-degree strip: iccp_ZpX(x0²·x1 + x0·x1, x0) = (1, x0²+x0, x1)
-- (strip x0, recurse: bucket gcd of x0+1, fold back — content is
-- x0·(x0+1); the d == 0 branch would extract only integer content)
#guard
  let p := MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0)) (st 1 [(1,1)] x0)
  iccpZpXM (zp 7) p 0 == (1, MPoly.add (MPoly.mul x0 x0) x0, x1)

-- bucket path: iccp_ZpX((x0²+x0+1)·x1, x0) = (1, x0²+x0+1, x1)
#guard
  let q := MPoly.add (MPoly.mul x0 x0) (MPoly.add x0 one)
  iccpZpXM (zp 7) (st 1 [(1,1)] q) 0 == (1, q, x1)

/-! ## modGcd (multivariate modular) + the mgcd_check differential -/

-- gcd((x+y)(x+1), (x+y)(y+1)) = x+y — exercises modGcdRec with
-- genuine interpolation (or the PRS fallback)
#guard
  let s := MPoly.add x0 x1
  let a := MPoly.mul s (MPoly.add x0 one)
  let b := MPoly.mul s (MPoly.add x1 one)
  gcdM none a b == s

-- gcd(x²−y², (x+y)²) = x+y
#guard
  let a := MPoly.sub (MPoly.mul x0 x0) (MPoly.mul x1 x1)
  let b := MPoly.pw (MPoly.add x0 x1) 2
  gcdM none a b == MPoly.add x0 x1

-- differential (z3's mgcd_check): the modular route agrees with
-- gcdPrsM on the same inputs
#guard
  let s := MPoly.add x0 x1
  let a := MPoly.mul s (MPoly.add x0 one)
  let b := MPoly.mul s (MPoly.add x1 one)
  gcdM none a b == gcdPrsM none a b 1
#guard
  let a := MPoly.sub (MPoly.mul x0 x0) (MPoly.mul x1 x1)
  let b := MPoly.pw (MPoly.add x0 x1) 2
  gcdM none a b == gcdPrsM none a b 1
#guard
  let a := MPoly.add (st 2 [(1,1)] (MPoly.mul x0 x0)) (st 4 [(1,1)] x0)
  let b := MPoly.add (st 1 [(1,1)] x0) (c 3)
  gcdM none a b == gcdPrsM none a b 1

end LeanNonlinearArith.Nlsat.Tests
