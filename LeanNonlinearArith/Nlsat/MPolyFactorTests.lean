import LeanNonlinearArith.Nlsat.MPolyFactor
import LeanNonlinearArith.Nlsat.Explain

/-!
# nla-12d.1b-v tests — factor layer + Explain.factor/add_zero_assumption pins

Yun decomposition with multiplicities (incl. the j-order of pieces),
univariate bridge via nla-27, the deg-2 discriminant split (and
irreducible case), constant/content drop in the distinct view,
deg-2-multivariate vs univariate dispatch, and the explain-side
factor cache + zero-assumption emission shapes.
-/

namespace LeanNonlinearArith.Nlsat.Tests

open LeanNonlinearArith.Kernel
open LeanNonlinearArith.Nlsat
open LeanNonlinearArith.Nlsat.Solver hiding run'
open LeanNonlinearArith.Nlsat.Explain hiding maxVarLits

private def x0 : MPoly := MPoly.ofVar 0
private def x1 : MPoly := MPoly.ofVar 1
private def c (n : Int) : MPoly := MPoly.ofInt n
private def one : MPoly := c 1
private def st (k : Int) (m : Monomial) (p : MPoly) : MPoly := MPoly.smulTerm k m p

/-! ## factorM: univariate -/

-- x²−1 → [x+1, x−1] (nla-27 order)
#guard MPoly.factorDistinct (MPoly.sub (MPoly.mul x0 x0) one)
    == #[MPoly.add x0 one, MPoly.sub x0 one]

-- (x+1)²(x+2): Yun emits P₁ = x+2 first, then P₂ = x+1 with mult 2
#guard MPoly.factorM (MPoly.mul (MPoly.pw (MPoly.add x0 one) 2) (MPoly.add x0 (c 2)))
    == ⟨1, #[(MPoly.add x0 (c 2), 1), (MPoly.add x0 one, 2)]⟩

-- irreducible univariate: x²+1 pushed as-is
#guard MPoly.factorDistinct (MPoly.add (MPoly.mul x0 x0) one)
    == #[MPoly.add (MPoly.mul x0 x0) one]

-- content: 2x+2 → constant 2 (dropped in the distinct view), [x+1]
#guard MPoly.factorM (MPoly.add (st 2 [] x0) (c 2))
    == ⟨2, #[(MPoly.add x0 one, 1)]⟩
#guard MPoly.factorDistinct (MPoly.add (st 2 [] x0) (c 2))
    == #[MPoly.add x0 one]

/-! ## factorM: multivariate -/

-- x²−y² → [x−y, x+y] via the deg-2 discriminant split (disc = 4y²)
#guard MPoly.factorDistinct (MPoly.sub (MPoly.mul x0 x0) (MPoly.mul x1 x1))
    == #[MPoly.sub x0 x1, MPoly.add x0 x1]

-- x²+y² → irreducible (disc = −4y² fails the sqrt quick check)
#guard MPoly.factorDistinct (MPoly.add (MPoly.mul x0 x0) (MPoly.mul x1 x1))
    == #[MPoly.add (MPoly.mul x0 x0) (MPoly.mul x1 x1)]

-- multivariate content: (x+1)·(y+1) → [y+1, x+1] (content factor
-- first — factorCore recurses on the content before the Yun piece)
#guard MPoly.factorDistinct (MPoly.mul (MPoly.add x0 one) (MPoly.add x1 one))
    == #[MPoly.add x1 one, MPoly.add x0 one]

-- deg-3-in-min-var piece: x³+y³ is square-free primitive with min-var
-- degree 3 ⇒ pushed back unfactored (z3's factor_n_sqf_pp TODO)
#guard
  let p := MPoly.add (MPoly.pw x0 3) (MPoly.pw x1 3)
  MPoly.factorDistinct p == #[p]

/-! ## Explain.factor cache + addZeroAssumption -/

-- factor memoization: two calls, one cache entry, same result
#guard Explain.run' (do
  Solver.init
  let p := MPoly.sub (MPoly.mul x0 x0) one
  let f1 ← factor p
  let f2 ← factor p
  let s ← liftS get
  return f1 == f2 && s.explainCache.factors.size == 1
    && f1 == #[MPoly.add x0 one, MPoly.sub x0 one])

-- addZeroAssumption at x0 := 1 on (x0−1)(x0+2): only the vanishing
-- factor is kept; negated single-factor EQ literal
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let p := MPoly.mul (MPoly.sub x0 one) (MPoly.add x0 (c 2))
  addZeroAssumption p
  let st ← get
  let s ← liftS get
  return st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.eq, [(MPoly.sub x0 one, false)]⟩))

-- multi-factor: (x0−1)·x1 at x0 := 1, x1 := 0 — both factors vanish ⇒
-- negated two-factor EQ literal (factor order: content factor first)
#guard Explain.run' (do
  Solver.init
  let c1 ← liftS (liftC (CellStore.fresh (.rat 1 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 0 c1 })
  let c0 ← liftS (liftC (CellStore.fresh (.rat 0 : RAlg)))
  liftS (modify fun s => { s with assignment := s.assignment.set 1 c0 })
  let p := MPoly.mul (MPoly.sub x0 one) x1
  addZeroAssumption p
  let st ← get
  let s ← liftS get
  return st.result == #[⟨1, true⟩]
    && s.atoms[1]! == some (.ineq ⟨.eq, [(x1, false), (MPoly.sub x0 one, false)]⟩))

end LeanNonlinearArith.Nlsat.Tests
