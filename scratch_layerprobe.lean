import LeanNonlinearArith.Tactic.NonlinearArith

/- nla-14 Slice 4 layer probes: which layer closes each driver?
Run AFTER `lake build LeanNonlinearArith.Tactic.NonlinearArith`:
`lake env lean scratch_layerprobe.lean`. -/

open LeanNonlinearArith.Nlsat.Frontend

/- L1 candidates (saturate-closable ℤ) -/
run_cmd nlaL2Runs.set 0
example (x : ℤ) : 0 ≤ x * x := by nonlinear_arith
run_cmd do IO.println s!"sqZ-nonneg: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (x y : ℤ) (h1 : 1 ≤ x) (h2 : 1 ≤ y) : x + y ≤ x * y + 1 := by nonlinear_arith
run_cmd do IO.println s!"tangent: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

/- Slice-3 drivers -/
run_cmd nlaL2Runs.set 0
example (x y : ℝ) (h : x * x + y * y < 0) : False := by nonlinear_arith
run_cmd do IO.println s!"sq: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (x y : ℝ) (h : x * x < 0 ∨ y * y < 0) : False := by nonlinear_arith
run_cmd do IO.println s!"disj: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (x : ℝ) (h : (x ≥ 1 ∧ x < 1) ∨ x * x < 0) : False := by nonlinear_arith
run_cmd do IO.println s!"proxy: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (x : ℤ) (h : x * x = 2) : False := by nonlinear_arith
run_cmd do IO.println s!"int1: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (x y : ℤ) (hx : x * x = 2) (hy : y * y = 3) : False := by nonlinear_arith
run_cmd do IO.println s!"int2: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (n : ℕ) (h : n * n = 2) : False := by nonlinear_arith
run_cmd do IO.println s!"nat: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (x y : ℝ) (h1 : x < y * y) (h2 : y * y < x - 1) : False := by nonlinear_arith
run_cmd do IO.println s!"reorder: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

run_cmd nlaL2Runs.set 0
example (y x : ℤ) (h1 : y < x) (h2 : x * x = 2) : False := by nonlinear_arith
run_cmd do IO.println s!"riii: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

/- B&B candidate that (maybe) defeats L1: x(x+1)=3 has the real root
(−1+√13)/2 but no integer one. -/
run_cmd nlaL2Runs.set 0
example (x : ℤ) (h : x * (x + 1) = 3) : False := by nonlinear_arith
run_cmd do IO.println s!"bb-cand: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"

/- o139 (slow — the 800k budget) -/
run_cmd nlaL2Runs.set 0
set_option maxHeartbeats 800000 in
example (a b c da db dc : ℝ)
    (h1 : a * db ≤ b * da) (h2 : b * dc ≤ c * db)
    (h3 : 0 < da) (h4 : 0 < db) (h5 : 0 < dc) :
    a * dc ≤ c * da := by nonlinear_arith
run_cmd do IO.println s!"o139: L2={← nlaL2Runs.get} conflicts={← nlaL2Conflicts.get}"
