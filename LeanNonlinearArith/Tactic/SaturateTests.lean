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

/-! ## slice 4: tangent planes at mined constants -/

-- the classic: tangent at (1,1)
example (x y : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y) : x + y ≤ x * y + 1 := by
  nla_saturate

-- explicit tangent bound, lower anchors
example (x y : ℤ) (hx : 2 ≤ x) (hy : 3 ≤ y) : 3 * x + 2 * y - 6 ≤ x * y := by
  nla_saturate

-- upper anchors give the same plane from the other side
example (x y : ℤ) (h1 : x ≤ 2) (h2 : y ≤ 3) : 3 * x + 2 * y - 6 ≤ x * y := by
  nla_saturate

-- mixed anchor: product bounded by a scaled factor
example (x y : ℤ) (h1 : 0 ≤ x) (h2 : y ≤ 5) : x * y ≤ 5 * x := by
  nla_saturate

/-! ## generator parity rows (RULES.md audit, 2026-07-24) -/

-- B5 zero-product split: disjunctive conclusion, omega case-splits
example (x y : ℤ) (h : x * y = 0) (hx : x ≠ 0) : y = 0 := by nla_saturate

-- const-substitution (B9/PL1/T1/MB6): other factor completely unbounded
example (x y : ℤ) (h1 : 3 ≤ x) (h2 : x ≤ 3) : x * y = 3 * y := by nla_saturate

-- square secant (Horner/H1 specimen: needs x² ≤ 2x on [0,2], which interval
-- bounds alone cannot give)
example (x : ℤ) (h1 : 0 ≤ x) (h2 : x ≤ 2) : -2 ≤ x - x ^ 2 := by nla_saturate

-- square tangent at a mined anchor (`_h` feeds the miner, not the proof
-- term — the tangent is globally valid once anchored)
example (x : ℤ) (_h : 3 ≤ x) : 6 * x - 9 ≤ x ^ 2 := by nla_saturate

/-! ## class C: down-propagation and pair rules (RULES.md audit) -/

-- O2 cancellation specimen: positive shared factor
example (x y z : ℤ) (h : x * z ≤ y * z) (hz : 0 < z) : x ≤ y := by nla_saturate

-- O2 with negative shared factor flips the comparison
example (x y z : ℤ) (h : x * z ≤ y * z) (hz : z < 0) : y ≤ x := by nla_saturate

-- O2 strict + shared factor on mixed sides (mul_comm alignment)
example (x y z : ℤ) (h : z * x < y * z) (hz : 0 < z) : x < y := by nla_saturate

-- O3 equality cancellation
example (x y z : ℤ) (h : x * z = y * z) (hz : 0 < z) : x = y := by nla_saturate

-- down-propagation, two-sided positive divisor: b ≤ ⌊8/2⌋
example (z b : ℤ) (h1 : 2 ≤ z) (h2 : z ≤ 4) (h3 : z * b ≤ 8) : b ≤ 4 := by
  nla_saturate

-- down-propagation, single-sided divisor from the lattice unit bound
example (z b : ℤ) (hz : 0 < z) (h : z * b ≤ 10) : b ≤ 10 := by nla_saturate

-- down-propagation, negative divisor
example (z b : ℤ) (h1 : -4 ≤ z) (h2 : z ≤ -2) (h3 : -8 ≤ z * b) : b ≤ 4 := by
  nla_saturate

-- down-sign: nonlinear sign division the leaf cannot do
example (a b : ℤ) (ha : 0 < a) (h : 1 ≤ a * b) : 1 ≤ b := by nla_saturate

-- MB4 square root, both conjuncts
example (x : ℤ) (h : x ^ 2 ≤ 9) : x ≤ 3 := by nla_saturate
example (x : ℤ) (h : x ^ 2 ≤ 9) : -3 ≤ x := by nla_saturate

-- MB5 square root, disjunctive clause resolved by a sign hypothesis
example (x : ℤ) (h : 10 ≤ x ^ 2) (hx : 0 ≤ x) : 4 ≤ x := by nla_saturate

/-! ## class D: failure-gated conditional clauses (RULES.md audit) -/

-- the class D specimen: sign clauses under indeterminate signs
example (x y : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) : x * y ≠ 0 := by nla_saturate

-- zero clause, contrapositive orientation (B6)
example (x y : ℤ) (h : x * y = 7) : x ≠ 0 := by nla_saturate

-- mixed known/unknown signs
example (x y : ℤ) (hx : 0 < x) (hy : y ≠ 0) : x * y ≠ 0 := by nla_saturate

-- B8: a nonzero cofactor cannot shrink the absolute value
example (x y : ℤ) (hx : x ≠ 0) (h : (x * y).natAbs ≤ 5) : y.natAbs ≤ 5 := by
  nla_saturate

-- B7: |x·y| = |x| with x ≠ 0 forces y = ±1
example (x y : ℤ) (h : (x * y).natAbs = x.natAbs) (hx : x ≠ 0) (hy : 1 < y) :
    False := by nla_saturate

-- O1 clause: mined pivot, cofactor sign unknown — x·y > 3·y under x ≤ 3
-- forces y < 0 (the disjunct choice matters, unlike a totality tautology)
example (x y : ℤ) (h : x ≤ 3) (h2 : 3 * y < x * y) : y < 0 := by
  nla_saturate

/-! ## review probes (2026-07-24 session review — lowest-confidence claims) -/

-- B1: ring_nf canonizes sign-flipped monomials to one atom
example (x y : ℤ) (h : (-x) * y ≤ 5) : -5 ≤ x * y := by nla_saturate

-- GE hypothesis through the pair scan (expected-type-hint normalization)
example (x y z : ℤ) (h : y * z ≥ x * z) (hz : 0 < z) : x ≤ y := by nla_saturate

-- Verus-scale literals through the corner fold
example (x y : ℤ) (h1 : 0 ≤ x) (h2 : x ≤ 18446744073709551615)
    (h3 : 0 ≤ y) (h4 : y ≤ 4294967296) :
    x * y ≤ 79228162514264337589248983040 := by nla_saturate

-- Verus-scale literals through down-prop interval division
example (z b : ℤ) (h1 : 4294967296 ≤ z) (h2 : z ≤ 18446744073709551615)
    (h3 : z * b ≤ 4294967296) : b ≤ 1 := by nla_saturate

-- tier interaction: an irrelevant bounded monomial (z*w) must not blow up
-- the clause retry for the x*y goal — this pinned the tiered-retry design
example (x y z w : ℤ) (hx : x ≠ 0) (hy : y ≠ 0) (h1 : 2 ≤ z) (h2 : z ≤ 4)
    (h3 : z * w ≤ 8) : x * y ≠ 0 ∧ w ≤ 4 := by
  constructor
  · nla_saturate
  · nla_saturate

/-! ## review round 2: miner blind spots (Eq and ¬-wrapped comparisons) -/

-- fixed var via Eq hyp (Z3 propagate_fixed_var parity)
example (x y : ℤ) (h : x = 3) : x * y = 3 * y := by nla_saturate

-- negated comparisons feed the miner (control-flow negations)
example (x y : ℤ) (h1 : ¬ (x < 2)) (h2 : ¬ (y < 3)) : 6 ≤ x * y := by
  nla_saturate

-- pair scan through ¬ (le_of_not_gt conversion)
example (x y z : ℤ) (h : ¬ (y * z < x * z)) (hz : 0 < z) : x ≤ y := by
  nla_saturate

/-! ## discharge-oracle scaling (DESIGN-discharge-oracle §3)

The cost-model stress goal: 8 monomials, lb+ub mined per factor. Before the
v0.5 oracle this blew the default heartbeat budget (~600 un-memoized omega
calls in generation, then an exponential min/max case-split in the omega
leaf); now it runs in ~2s. If this times out again, a scaling regression
crept in. -/

example (a b c d e f : ℤ)
    (ha : 1 ≤ a) (ha' : a ≤ 10) (hb : 2 ≤ b) (hb' : b ≤ 8)
    (hc : 0 ≤ c) (hc' : c ≤ 5) (hd : -3 ≤ d) (hd' : d ≤ 3)
    (he : 1 ≤ e) (he' : e ≤ 4) (hf : -2 ≤ f) (hf' : f ≤ 2) :
    a * b + c * d + e * f + a * c + b * e + d * f + a * e + b * c ≤ 500 := by
  nla_saturate

/-! ## pinned assumptions (if these break, the tactic's leaf design breaks) -/

-- omega atomizes syntactically-identical nonlinear terms; nla_saturate's leaf
-- relies on this instead of explicit generalization
example (x y : ℤ) (h : x * y ≤ 5) : x * y ≤ 6 := by omega

-- robustness: quantified hypotheses with products under binders are ignored,
-- not fatal
example (x y : ℤ) (hq : ∀ i : ℤ, x * i ≤ x * i) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ x * y := by nla_saturate

/-! ## multi-round saturation (rounds-to-fixpoint, order independence)

A single sequential generation pass is Gauss-Seidel: facts noted for
monomial i feed only monomials processed later in the ring_nf-determined
context order. Z3's saturation is fixpoint-driven, so chains running
*against* the processing order are the multi-round witness class. Here h0
is written in ring_nf normal form (stays in place) while hxy gets
rewritten and re-inserted at the end of the context — so the tangent
target x*w is processed before the down-prop source x*y. Round 1 derives
x ≤ 5 (down-prop from x*y ≤ 10, 2 ≤ y); round 2 anchors the tangent
plane 5*w + 3*x - 15 ≤ x*w on x*w. Fails on the single-round tactic
(probe-confirmed, this slice) — the O1 clause tiers have no lower bound
for x*w in the region x, w ≥ 1. -/
example (x y w r : ℤ) (h0 : 15 + x*w ≤ x*3 + w*5 + r)
    (hw : w ≤ 3) (hy : 2 ≤ y) (hxy : y*x ≤ 10) : 0 ≤ r := by
  nla_saturate

-- forward-order variant of the same chain (closed by round 1 already —
-- pins the Gauss-Seidel behavior so an ordering change can't hide behind
-- the loop)
example (x y w r : ℤ) (hw : w ≤ 3) (hy : 2 ≤ y) (hxy : x*y ≤ 10)
    (h0 : x*w + 15 ≤ 3*x + 5*w + r) : 0 ≤ r := by
  nla_saturate

-- n-ary down-propagation chain through an unbounded factor: x*y ≤ 10
-- derived from (x*y)*z ≤ 30 and z ≥ 3, then x ≤ 5 from y ≥ 2; the O1
-- pivot clauses also close this disjunctively, so it pins whichever
-- path fires first
example (x y z : ℤ) (hy : 2 ≤ y) (hz : 3 ≤ z)
    (h : x * y * z ≤ 30) : x ≤ 5 := by
  nla_saturate

-- explicit round bound: the order-reversed chain needs two productive
-- rounds; `nla_saturate 1` must NOT close it (guards that the loop is
-- really doing the work, and that the bound is honored)
example (x y w r : ℤ) (h0 : 15 + x*w ≤ x*3 + w*5 + r)
    (hw : w ≤ 3) (hy : 2 ≤ y) (hxy : y*x ≤ 10) : 0 ≤ r := by
  fail_if_success nla_saturate 1
  nla_saturate

/-! ## multi-round saturation (Gauss-Seidel order-dependence removed)

A single sequential pass only feeds facts forward along the ring_nf-determined
context order. These specimens need a fact derived from a LATER monomial to
re-anchor rules on an EARLIER one — round 2 work by construction. -/

-- order-reversed chain: h0 is already in ring_nf normal form (stays first),
-- hxy is rewritten (moves to the context tail), so the tangent target x*w is
-- processed before the down-prop source x*y. Round 1: x ≤ 5 from
-- x*y ≤ 10 ∧ 2 ≤ y; round 2: tangent on x*w anchored at (5, 3). The O1
-- clause tiers cannot rescue this one — they only emit single-pivot bounds,
-- and the region x, w ≥ 1 needs the two-anchor corner lower bound.
example (x y w r : ℤ) (h0 : 15 + x*w ≤ x*3 + w*5 + r)
    (hw : w ≤ 3) (hy : 2 ≤ y) (hxy : y*x ≤ 10) : 0 ≤ r := by
  nla_saturate

-- same chain, forward order (single round suffices) — pins that the rounds
-- loop terminates at fixpoint without disturbing the order-aligned path
example (x y w r : ℤ) (hxy : x*y ≤ 10) (hy : 2 ≤ y) (hw : w ≤ 3)
    (h0 : 15 + x*w ≤ x*3 + w*5 + r) : 0 ≤ r := by
  nla_saturate

-- explicit round-bound syntax
example (x y w r : ℤ) (h0 : 15 + x*w ≤ x*3 + w*5 + r)
    (hw : w ≤ 3) (hy : 2 ≤ y) (hxy : y*x ≤ 10) : 0 ≤ r := by
  nla_saturate 4
