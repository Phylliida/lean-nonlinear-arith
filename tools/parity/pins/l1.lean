import LeanNonlinearArith

-- nla-16 stats-channel pin: L1 close (sqZ specimen).
example (x : ℤ) : 0 ≤ x * x := by nonlinear_arith
