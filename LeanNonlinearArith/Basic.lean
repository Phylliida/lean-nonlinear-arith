/-
lean-nonlinear-arith: Z3's nonlinear_arith, reconstructed in Lean.

Library layout (see DESIGN.md):
  Templates    -- nla lemma schemas (sign, order, monotonicity, tangent, division)
  Kernel       -- computational Q[x]: dense polys, gcd, squarefree, psc chains
  RootCounting -- certified root counting/isolation (IVT lower, Rolle-chain upper, Sturm)
  Projection   -- S1: psc projection soundness (delineability)
  Solver       -- unverified search: saturation loop, simplex/Farkas, nlsat port
  Checker      -- trace -> kernel-checked proofs
  Tactic       -- `nonlinear_arith` front-end, Int -> Real relaxation
-/

def LeanNonlinearArith.version : String := "0.0.1"
