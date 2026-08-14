import LeanNonlinearArith

-- nla-16 stats-channel pin: L2 close (B&B driver, exactly 1 conflict).
example (x : ℤ) (h : x * (x + 1) = 3) : False := by nonlinear_arith
