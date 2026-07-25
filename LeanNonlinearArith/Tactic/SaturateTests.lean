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

/-! ## div/mod collection (RULES D4/D5 + the core div/mod axiomatization)

Symbolic divisors only — literal divisors are omega-native at the leaf
(pinned first). Every rule family: defining equation, sign-gated mod range,
const-substitution at a point-mined divisor, D4/D5 interval-quotient bounds,
and div atoms as monomial factors. -/

-- literal divisor: omega-native, no rules involved
example (x : ℤ) (h : x ≤ 10) : x / 5 ≤ 2 := by nla_saturate

-- mod range, positive symbolic divisor
example (x y : ℤ) (hy : 0 < y) : x % y < y := by nla_saturate
example (x y : ℤ) (hy : 0 < y) : 0 ≤ x % y := by nla_saturate

-- mod range, negative symbolic divisor (via Int.emod_neg flip)
example (x y : ℤ) (hy : y < 0) : x % y < -y := by nla_saturate

-- remainder lower bound from a bare ≠ 0 (lattice-inconclusive path); the
-- unused-variable lint is a false positive — the linter only tracks
-- syntactic uses, and hy enters through the meta-built noted proof (the
-- goal is FALSE without hy: x = -1, y = 0)
set_option linter.unusedVariables false in
example (x y : ℤ) (hy : y ≠ 0) : 0 ≤ x % y := by nla_saturate

-- defining equation y * (x / y) + x % y = x (unconditional — holds at y = 0)
example (x y : ℤ) (h : x % y = 0) : y * (x / y) = x := by
  nla_saturate

-- const-substitution: point-mined divisor collapses to omega-native literal
example (x y : ℤ) (hy : y = 7) (h : x ≤ 20) : x / y ≤ 2 := by nla_saturate

-- D4 upper quotient bound (nonneg dividend needs only the divisor lb)
example (x y : ℤ) (hy : 2 ≤ y) (hx : x ≤ 10) : x / y ≤ 5 := by nla_saturate

-- D4, negative dividend (max over the divisor RANGE: q = hx / hy)
example (x y : ℤ) (hy : 2 ≤ y) (hy' : y ≤ 4) (hx : x ≤ -1) : x / y ≤ -1 := by
  nla_saturate

-- D5 lower quotient bounds
example (x y : ℤ) (hy : 2 ≤ y) (hx : 0 ≤ x) : 0 ≤ x / y := by nla_saturate
example (x y : ℤ) (hy : 2 ≤ y) (hy' : y ≤ 5) (hx : 20 ≤ x) : 4 ≤ x / y := by
  nla_saturate

-- div atom as a monomial factor: quotient sign feeds the product sign rule
example (x y z : ℤ) (hy : 0 < y) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    0 ≤ (x / y) * z := by nla_saturate

-- quotient interval bounds feed the product corner machinery: div pairs are
-- generated before the monomial loop, so x/y ∈ [0, 6] anchors the corner on
-- (x/y) * w within round 1
example (x y w : ℤ) (hy : 3 ≤ y) (hy' : y ≤ 5) (hx : 0 ≤ x) (hx' : x ≤ 20)
    (hw : 0 ≤ w) (hw' : w ≤ 2) : (x / y) * w ≤ 12 := by nla_saturate

-- review-round pins: shapes predicted to be gaps that the composed
-- machinery already covers. (i) strict positivity is mined as lb 1, so the
-- divisor lower bound is present whenever the lattice is pos; (ii/iii)
-- negative dividends fall to the defining equation + sign clauses on
-- y * (x / y); (iv) nested pairs collect postorder; (v) mod range feeds
-- the product sign rule.
example (x y : ℤ) (hy : 0 < y) (hx : x ≤ 10) : x / y ≤ 10 := by nla_saturate
example (x y : ℤ) (hy : 2 ≤ y) (hx : x ≤ -1) : x / y ≤ -1 := by nla_saturate
example (x y : ℤ) (hy : 0 < y) (hx : -10 ≤ x) : -10 ≤ x / y := by nla_saturate
example (x y z : ℤ) (hy : 2 ≤ y) (hz : 2 ≤ z) (hx : 0 ≤ x) (hx' : x ≤ 40) :
    x / y / z ≤ 10 := by nla_saturate
example (x y z : ℤ) (hy : 0 < y) (hz : 0 ≤ z) : 0 ≤ (x % y) * z := by
  nla_saturate

/-! ## k ≥ 3 power envelopes and roots (MB1-2/MB4/MB5 at general exponents)

Z3's monomial_bounds interval powers and root propagation are k-generic;
k = 2 keeps its tighter secant/tangent path. Roots use the contrapositive
`u < (r+1)^p` pattern with meta-computed integer k-th roots. -/

-- odd interval-pow envelopes
example (x : ℤ) (h : x ≤ 3) : x ^ 3 ≤ 27 := by nla_saturate
example (x : ℤ) (h : -2 ≤ x) : -8 ≤ x ^ 3 := by nla_saturate

-- even envelope ub (M = max |lo| |hi| — the negative side dominates here)
example (x : ℤ) (h1 : -3 ≤ x) (h2 : x ≤ 2) : x ^ 4 ≤ 81 := by nla_saturate

-- even envelope lb, positive and negative sides
example (x : ℤ) (h : 2 ≤ x) : 16 ≤ x ^ 4 := by nla_saturate
example (x : ℤ) (h : x ≤ -2) : 16 ≤ x ^ 4 := by nla_saturate

-- MB4 odd root, incl. a negative bound (floor root over ℤ)
example (x : ℤ) (h : x ^ 3 ≤ 30) : x ≤ 3 := by nla_saturate
example (x : ℤ) (h : x ^ 3 ≤ -7) : x ≤ -2 := by nla_saturate

-- MB4 even root, both conjuncts
example (x : ℤ) (h : x ^ 4 ≤ 80) : x ≤ 2 := by nla_saturate
example (x : ℤ) (h : x ^ 4 ≤ 80) : -2 ≤ x := by nla_saturate

-- MB5 odd root (ceil root: 3^3 = 27 < 30 forces 4)
example (x : ℤ) (h : 30 ≤ x ^ 3) : 4 ≤ x := by nla_saturate

-- MB5 even root: genuinely disjunctive, resolved by a sign hypothesis
example (x : ℤ) (h : 17 ≤ x ^ 4) (hx : 0 ≤ x) : 3 ≤ x := by nla_saturate

-- k = 5 at scale
example (x : ℤ) (h : x ^ 5 ≤ 100000) : x ≤ 10 := by nla_saturate

-- code-review fix (2026-07-25): defining equation noted in BOTH product
-- orientations — ring_nf canonizes user-written products of y and x / y to
-- its own order, which need not match the meta-built form; each atom form
-- needs its own bridge (the second example failed before the fix)
example (x y : ℤ) (h : y * (x / y) ≤ 5) : x - x % y ≤ 5 := by nla_saturate
example (x y : ℤ) (h : (x / y) * y ≤ 5) : x - x % y ≤ 5 := by nla_saturate

/-! ### Oracle v1: derived-bound anchors (DESIGN-discharge-oracle §2b/§3)

Syntactic mining is structurally incomplete for bounds that are implied but
written nowhere; the oracle propagates the linear closure and its tightest
per-atom bounds join every anchor set. All five examples probe-confirmed
failing without the oracle (2026-07-25). -/

-- derived lower bound as an order-rule anchor (7 ≤ b is written nowhere)
example (a b c : ℤ) (h1 : a ≤ b - 2) (h2 : 5 ≤ a) (h3 : 2 ≤ c) :
    14 ≤ b * c := by nla_saturate

-- derived fixed var (a = 4 from a + b = 7 with b pinned) → const-subst
example (a b c : ℤ) (h1 : a + b = 7) (h2 : 3 ≤ b) (h3 : b ≤ 3) :
    a * c = 4 * c := by nla_saturate

-- coefficient rounding in propagation (3a ≥ 4 ⟹ a ≥ ⌈4/3⌉ = 2)
example (a b : ℤ) (h1 : 5 ≤ 3 * a + 1) (h2 : 2 ≤ b) : 4 ≤ a * b := by
  nla_saturate

-- derived pivot feeding a tier-2 O1 clause (sign-unknown cofactor c)
example (a b c : ℤ) (h1 : b ≤ a + 2) (h2 : a ≤ 5) (h3 : 0 ≤ b)
    (h4 : 21 ≤ b * c) (h5 : c ≤ 3) : 3 ≤ c := by nla_saturate

-- derived anchor for the square tangent envelope (b ≥ 4 ⟹ 8b - 16 ≤ b²)
example (a b : ℤ) (h1 : a ≤ b - 1) (h2 : 3 ≤ a) : 16 ≤ b ^ 2 := by
  nla_saturate

/-! ### Oracle v1: O4 ±-equivalences (RULES O4, Z3 evars/generate_mon_ol)

The oracle's parity union-find derives unit ±-equalities; fully-equivalent
monomial pairs bridge eagerly as `q = ±p` (Z3's emonics canonization),
one-equiv-factor pairs get the model-free order-transfer clauses in tier 2.
All five probe-confirmed failing without the evars pass (2026-07-25). -/

-- eager mul bridge (d ≡ -c derived → a*d = -(a*c))
example (a c d : ℤ) (h1 : d = -c) (h2 : 3 ≤ a * c) : a * d ≤ -3 := by
  nla_saturate

-- eager pow bridges: symbolic bound, only the bridge can close these
example (c d x : ℤ) (h1 : d = -c) (h2 : c ^ 2 ≤ x) : d ^ 2 ≤ x := by
  nla_saturate
example (c d x : ℤ) (h1 : d = -c) (h2 : x ≤ c ^ 3) : d ^ 3 ≤ -x := by
  nla_saturate

-- order-transfer clause: one equiv factor, free cofactors (tier 2)
example (a b c d : ℤ) (h1 : d = -c) (h2 : 0 < c) (h3 : a + b ≤ -1) :
    a * c < b * d := by nla_saturate

-- equivalence through the union-find chain (d = e, e = -c)
example (a c d e : ℤ) (h1 : d = e) (h2 : e = -c) (h3 : 3 ≤ a * c) :
    a * d ≤ -3 := by nla_saturate
