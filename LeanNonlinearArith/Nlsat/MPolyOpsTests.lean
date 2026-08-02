import LeanNonlinearArith.Nlsat.MPolyOps

/-!
# nla-12d.1b-i tests — MPoly foundations pins

Monomial div/sqrt/pw, graded-lex extremal terms, derivative, integer
content, exact division + divides, the pseudo-division identity
(`lc(q)^d · p = Q·q + R`), and the sqrt attempt (square / non-square /
sign cases). Expected values are built with the same canonicalizing
ops so representations line up.
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def x2 : MPoly := MPoly.ofVar 2
private def c (n : Int) : MPoly := MPoly.ofInt n
private def one : MPoly := c 1
private def st (k : Int) (m : Monomial) (p : MPoly) : MPoly := MPoly.smulTerm k m p

/-! ## Monomial ops -/

#guard Monomial.div? [(0,2),(1,1)] [(1,1)] == some [(0,2)]
#guard Monomial.div? [(0,2)] [(0,3)] == none
#guard Monomial.div? [(0,2)] [] == some [(0,2)]
#guard Monomial.div? [(0,1)] [(1,1)] == none
#guard Monomial.isSquare [(0,2),(1,4)] && !Monomial.isSquare [(0,1)]
#guard Monomial.sqrt [(0,2),(1,4)] == some [(0,1),(1,2)]
#guard Monomial.sqrt [(0,3)] == none
#guard Monomial.sqrt [] == some []
#guard Monomial.divXk [(0,3),(1,1)] 0 2 == [(0,1),(1,1)]
#guard Monomial.divXk [(0,3),(1,1)] 0 3 == [(1,1)]
#guard Monomial.pw [(0,1),(1,2)] 2 == [(0,2),(1,4)]

/-! ## glex extremal terms, derivative, pw -/

-- biggest var dominates at equal total degree (x1 > x0)
#guard (MPoly.add x0 x1).glexMaxTerm == some (1, [(1,1)])
    && (MPoly.add x0 x1).glexMinTerm == some (1, [(0,1)])
#guard (MPoly.add (MPoly.mul x0 x0) x1).glexMaxTerm == some (1, [(0,2)])
#guard (MPoly.zero : MPoly).glexMaxTerm == none

-- d/dx0 (3·x0²·x1 + 2·x0 + 5) = 6·x0·x1 + 2
#guard MPoly.derivative (MPoly.add (st 3 [(1,1)] (MPoly.mul x0 x0))
    (MPoly.add (st 2 [] x0) (c 5))) 0
  == MPoly.add (st 6 [(1,1)] x0) (c 2)

#guard MPoly.pw (MPoly.add x0 one) 2
  == MPoly.add (MPoly.mul x0 x0) (MPoly.add (st 2 [] x0) one)
#guard MPoly.pw x0 0 == one && MPoly.pw x0 1 == x0

/-! ## integer content -/

#guard MPoly.ic (MPoly.add (st 4 [] x0) (c 6)) == 2
#guard MPoly.ic (MPoly.sub (c 2) (st 4 [] x0)) == 2   -- gcd nonneg
#guard MPoly.icStrip (MPoly.add (st 4 [] x0) (c 6))
    == (2, MPoly.add (st 2 [] x0) (c 3))
#guard MPoly.icStrip (c (-6)) == (-6, one)             -- const keeps sign
#guard MPoly.icStrip MPoly.zero == (0, MPoly.zero)
#guard MPoly.exactDivScalar (MPoly.add (st 4 [] x0) (c 6)) 2
    == MPoly.add (st 2 [] x0) (c 3)

/-! ## var analysis -/

#guard (MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0)) (st 1 [(2,1)] (MPoly.pw x1 3))).varDegrees
    == #[(0,2),(1,3),(2,1)]
#guard (MPoly.add (st 1 [(1,1)] (MPoly.mul x0 x0)) (st 1 [(2,1)] (MPoly.pw x1 3))).getMinDegreeVar
    == some 2
#guard (MPoly.add x0 x1).getMinDegreeVar == some 0   -- tie → earliest

/-! ## exact division + divides -/

private def x0sq : MPoly := MPoly.mul x0 x0
private def x1sq : MPoly := MPoly.mul x1 x1
private def sum01 : MPoly := MPoly.add x0 x1

#guard MPoly.divides sum01 (MPoly.sub x0sq x1sq)
#guard MPoly.exactDiv (MPoly.sub x0sq x1sq) sum01 == MPoly.sub x0 x1
#guard !MPoly.divides sum01 (MPoly.add x0sq x1sq)
#guard MPoly.divides (c 2) (st 4 [] x0)
#guard MPoly.exactDiv (st 4 [] x0) (c 2) == st 2 [] x0
#guard !MPoly.divides (c 2) (st 3 [] x0)

/-! ## pseudo_division_core -/

private def pP : MPoly := MPoly.add (st 2 [] x0sq) (MPoly.add (st 3 [] x0) one)
private def pQ : MPoly := MPoly.add (st 2 [] x0) one

-- the identity lc(q)^d · p = Q·q + R with the returned d
#guard
  let (d, Q, R) := MPoly.pseudoDivisionCore pP pQ 0 false true
  d == 2 && R == MPoly.zero
    && Q == MPoly.add (st 4 [] x0) (c 4)
    && MPoly.mul (MPoly.pw (c 2) d) pP == MPoly.add (MPoly.mul Q pQ) R

-- exactD top-up: iterations (1) < exact_d (2); identity holds at exact_d
-- (z3 returns d at the iteration count — documented)
#guard
  let p := MPoly.add (st 2 [] x0sq) (MPoly.add x0 one)
  let (d, Q, R) := MPoly.pseudoDivisionCore p pQ 0 true true
  d == 1 && R == c 4 && Q == st 4 [] x0
    && MPoly.mul (MPoly.pw (c 2) 2) p == MPoly.add (MPoly.mul Q pQ) R

-- pseudoRemainder (exactD=false): untopped remainder + iteration count
#guard
  let p := MPoly.add (st 2 [] x0sq) (MPoly.add x0 one)
  MPoly.pseudoRemainder p pQ 0 == (1, c 2)

-- exactPseudoRemainder = the topped R
#guard
  let p := MPoly.add (st 2 [] x0sq) (MPoly.add x0 one)
  MPoly.exactPseudoRemainder p pQ 0 == c 4

-- deg_B == 0 (const q): Q = p·q^(d−1), R = 0, d = deg_A + 1
#guard
  let p := MPoly.add x0sq one
  MPoly.pseudoDivisionCore p (c 3) 0 true true == (3, MPoly.mul p (c 9), MPoly.zero)

-- deg_B > deg_A: Q = 0, R = p, d = 0
#guard MPoly.pseudoDivisionCore x0 x0sq 0 false true == (0, MPoly.zero, x0)

/-! ## sqrt -/

-- (x0 + x1)² → x0 + x1
#guard MPoly.sqrt (MPoly.pw sum01 2) == some sum01

-- (2·x0 + x1)² = 4x0² + 4x0x1 + x1² → 2·x0 + x1
#guard
  let p := MPoly.add (st 4 [] x0sq) (MPoly.add (st 4 [] (MPoly.mul x0 x1)) x1sq)
  MPoly.sqrt p == some (MPoly.add (st 2 [] x0) x1)

-- x0² + 1: the constant remainder is not divisible by 2·m₁ → none
#guard MPoly.sqrt (MPoly.add x0sq one) == none

-- x0² + x0x1 + x1²: odd cross coefficient fails the 2a division → none
#guard MPoly.sqrt (MPoly.add x0sq (MPoly.add (MPoly.mul x0 x1) x1sq)) == none

-- negative extremal coefficient → none; const square → its root; zero → zero
#guard MPoly.sqrt (MPoly.neg x0sq) == none
#guard MPoly.sqrt (c 9) == some (c 3)
#guard MPoly.sqrt MPoly.zero == some MPoly.zero

/-! ## psc chains (12d.5 engine) -/

-- resultant = the reversed chain's head (z3 pushes then reverses);
-- values verified by hand: Res(x²−2, 2x) = −8, Res(x³−2, 3x²) = 108,
-- Res(x²+1, x²−1) = 4, Res(x⁴+1, x³+1) = 2 (chain [2, 1])
#guard MPoly.pscChain (MPoly.sub (MPoly.mul x0 x0) (c 2)) (st 2 [] x0) 0
    == #[c (-8)]
#guard MPoly.pscChain (MPoly.sub (MPoly.pw x0 3) (c 2)) (st 3 [] (MPoly.mul x0 x0)) 0
    == #[c 108]
#guard MPoly.pscChain (MPoly.add (MPoly.mul x0 x0) one)
    (MPoly.sub (MPoly.mul x0 x0) one) 0
    == #[c 4]
#guard MPoly.pscChain (MPoly.add (MPoly.pw x0 4) one)
    (MPoly.add (MPoly.pw x0 3) one) 0
    == #[c 2, one]

end LeanNonlinearArith.Nlsat.Tests
