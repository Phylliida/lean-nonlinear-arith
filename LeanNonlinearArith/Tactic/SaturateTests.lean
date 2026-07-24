import LeanNonlinearArith.Tactic.Saturate

/-!
# nla-05 slice-1 regression tests

Each example exercises one leg of the v0 pipeline: sign rules, zero rules,
squares, nested monomials (inner-first noting feeds outer premises via
`assumption`), omega-side premise derivation, and linear reasoning over
abstracted monomials.
-/

-- sign rules, direct premises
example (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x * y := by nla_saturate
example (x y : ℤ) (hx : 0 < x) (hy : y < 0) : x * y < 0 := by nla_saturate
example (x y : ℤ) (hx : x < 0) (hy : y < 0) : 0 < x * y := by nla_saturate
example (x y : ℤ) (hx : x ≤ 0) (hy : 0 ≤ y) : x * y ≤ 0 := by nla_saturate

-- zero rules
example (x y : ℤ) (h : x = 0) : x * y = 0 := by nla_saturate
example (x y : ℤ) (h : y = 0) : x * y = 0 := by nla_saturate

-- squares, no hypotheses at all
example (x : ℤ) : 0 ≤ x * x := by nla_saturate

-- omega derives the premise (2 ≤ x gives 0 ≤ x, strictness too)
example (x y : ℤ) (hx : 2 ≤ x) (hy : 3 ≤ y) : 0 < x * y := by nla_saturate

-- nested monomial: 0 ≤ x*y noted first, then feeds (x*y)*z
example (x y z : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ x * y * z := by nla_saturate

-- linear reasoning over the abstracted monomial
example (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x * y ≤ 5) :
    x * y + 1 ≤ 6 := by nla_saturate

-- sign fact combines with linear context at the leaf
example (x y c : ℤ) (hx : 0 < x) (hy : 0 < y) (hc : x * y ≤ c) :
    1 ≤ c := by nla_saturate

/-! ## slice 2: mined-constant order/interval rules -/

-- lower bounds, nonneg constants
example (x y : ℤ) (hx : 2 ≤ x) (hy : 3 ≤ y) : 6 ≤ x * y := by nla_saturate

-- upper bounds, nonneg factors
example (x y : ℤ) (h1 : 0 ≤ x) (h2 : x ≤ 5) (h3 : 0 ≤ y) (h4 : y ≤ 7) :
    x * y ≤ 35 := by nla_saturate

-- upper bounds, nonpos constants (negative × negative)
example (x y : ℤ) (hx : x ≤ -2) (hy : y ≤ -3) : 6 ≤ x * y := by nla_saturate

-- full corners on a symmetric box
example (x y : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) :
    x * y ≤ 1 := by nla_saturate
example (x y : ℤ) (h1 : -1 ≤ x) (h2 : x ≤ 1) (h3 : -1 ≤ y) (h4 : y ≤ 1) :
    -1 ≤ x * y := by nla_saturate

-- strict hypotheses feed non-strict mining via omega
example (x y : ℤ) (hx : 1 < x) (hy : 2 < y) : 6 ≤ x * y := by nla_saturate

/-! ## slice 3: ring_nf front-end + power monomials -/

-- even power, no hypotheses
example (x : ℤ) : 0 ≤ x ^ 2 := by nla_saturate

-- odd powers with sign hypotheses
example (x : ℤ) (h : 0 < x) : 0 < x ^ 3 := by nla_saturate
example (x : ℤ) (h : x < 0) : x ^ 3 < 0 := by nla_saturate

-- zero base
example (x : ℤ) (h : x = 0) : x ^ 2 = 0 := by nla_saturate

-- ring_nf turns x*x into x^2
example (x : ℤ) : 0 ≤ x * x + 1 := by nla_saturate

-- commutative canonization: y*x and x*y meet after ring_nf
example (x y : ℤ) (h : y * x ≤ 5) :
    x * y ≤ 5 := by nla_saturate

-- sum of squares
example (x y : ℤ) : 0 ≤ x ^ 2 + y ^ 2 := by nla_saturate

-- mixed: power and product together
example (x y : ℤ) (hx : 0 < x) (hy : 0 < y) : 0 < x ^ 2 * y := by nla_saturate
