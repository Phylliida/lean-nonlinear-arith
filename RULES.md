# RULES.md — Z3 nla generator ↔ Lean lemma correspondence (nla-20)

This table is the "Z3 ⊆ calculus" half of the containment argument: every
lemma Z3's nonlinear module can emit is an instance of a schema below, and
every schema gets a proven Lean lemma family in `Templates/`. Provenance is
`z3/src/math/lp/` at the workspace checkout (2026-02); the shipped verus-dev
Z3 is 4.12.5 — version deltas are flagged where they exist.

Two standing facts that make the table sufficient:

1. **Emission conditions are not soundness conditions.** Z3 consults the
   current rational model, throttles (`nla_throttle`), and randomizes order to
   decide *which* instances to emit; the clauses themselves are valid
   unconditionally. The Lean port proves each schema universally and may
   instantiate more freely — superset by construction.
2. **Canonization is hypothesis-side.** `lemma &= m` / `lemma &= f` attach the
   monomial-defining equations and ±sign var-equivalences (emons/evars) as
   antecedents. The Lean saturation loop supplies the same equations from its
   own monomial bookkeeping (nla-05); no schema depends on canonization magic.

Notation: `m = x₁·…·xₙ` is a monomial variable with its defining product;
`v(x)` denotes a rational constant baked into an emitted instance (the model
value at emission time — universally quantified in the schema).

## basics — nla_basics_lemmas.cpp

| id | source | schema (valid formula) | Lean form | status |
|----|--------|------------------------|-----------|--------|
| B1 | generate_sign_lemma :151 | m, n same var multiset up to sign flips with aggregate sign s ⟹ m = s·n | `List.prod` under permutation + negations | proven: `Basics.prod_eq_signs_mul_prod` |
| B2 | sign model-based :81, strict-case-zero :183 | strict signs of all factors determine strict sign of product (zero factor ⟹ zero product as degenerate case) | sign-of-product = product-of-signs over `LinearOrderedCommRing` | proven: `Basics.prod_pos_of_all_pos`, `Basics.prod_pos_iff_even_negs` |
| B3 | trivial zero :177 | x = 0 → x·y = 0 | `zero_mul`/`mul_eq_zero_of_left` | proven: `Basics.zero_factor`, `Basics.zero_factor_list` |
| B4 | fixed zero :196 | factor fixed to 0 (bound hyps) → m = 0 | B3 + bound hypotheses | proven: `Basics.zero_factor` + bound hyps |
| B5 | mon zero :222, :459 | m = 0 → ⋁ᵢ xᵢ = 0 | `prod_eq_zero_iff` (no zero divisors) | proven: `Basics.prod_zero_factor` |
| B6 | non-zero derived :294 | (contrapositive of B3 against m bounded away from 0) | same lemma, clause orientation | proven: B3 lemmas, clause orientation |
| B7 | neutral :316 | \|x·a\| = \|x\| ∧ x ≠ 0 → a = 1 ∨ a = −1 (all-int for >2 factors; pairs over ℝ) | `Int.eq_one_or_self_of...`-style cancellation | proven: `Basics.neutral_factor` |
| B8 | proportion generate_pl :388/:416 | over ℤ: (∀ j≠k, xⱼ ≠ 0) → \|m\| ≥ \|xₖ\| | `Int.le_of_dvd`-style abs bound | proven: `Basics.abs_le_abs_mul_of_ne_zero` |
| B9 | neutral-from-factors :509(:514) / :635(:644) | at most one factor f_i off ±1: (∧_{j≠i} f_j = c_j, c_j ∈ {1,−1}) → m = (∏c_j)·f_i (or m = ∏c_j when all are ±1) | ±1-substitution collapse of `List.prod` | n/a — instantiation-time subst+`ring` |
| B9b | neutral monic-to-factor :529(:559) | \|m\| = \|u\| ∧ m ≠ 0 → \|v\| = 1 — same validity as B7, model-based clause orientation. **Apparent dead code in current Z3**: guard `j == null_lpvar` at :544 can never hold (`j = var(fc)`), so `u` is never assigned and the function always returns false. Covered by B7 regardless; no port obligation. | B7 | noted |
| B10 | zero chain :670 | x = 0 → x·… = 0 (n-ary B3) | B3 generalized | proven: `Basics.zero_factor_list` |

## order — nla_order_lemmas.cpp

| id | source | schema | Lean form | status |
|----|--------|--------|-----------|--------|
| O1 | binomial sign :82 | for constant a: y ≤ 0 ∨ x > a ∨ xy ≤ a·y (4 sign variants) | mul-mono with constant pivot | proven: `Order.mul_le_pivot_of_pos` +3 variants |
| O2 | generate_ol :290 | c > 0 ∧ ac ≥ bc → a ≥ b; c < 0 dual; 4 variants | `le_div_iff`-free cancellation: `mul_le_mul_right` family | proven: `Order.le_of_mul_le_mul_pos` +3 variants |
| O3 | generate_ol_eq :265 | a·sign_a = b·sign_b ∧ c ≠ 0 → ac = bc | `mul_left_cancel₀` orientation | n/a — `congrArg` at instantiation |
| O4 | generate_mon_ol :180 | \|c\| = \|d\| ∧ sign-adjusted a < b → ac ≤ bd (order transfer between monomials sharing an equivalent factor) | composed from O2 + B1 | proven: `Order.order_transfer(_le)` + B1 rewrite |

## monotone — nla_monotone_lemmas.cpp

| id | source | schema | Lean form | status |
|----|--------|--------|-----------|--------|
| M1 | :62 | (∧ᵢ \|xᵢ\| ≤ \|vᵢ\|, model consts vᵢ) → \|m\| ≤ \|∏vᵢ\| | abs-product monotonicity, `List` fold | proven: `Monotone.abs_mul_le`, `Monotone.abs_prod_le` |
| M2 | :84 | dual: (∧ᵢ \|xᵢ\| ≥ \|vᵢ\|) → \|m\| ≥ \|∏vᵢ\| | dual | proven: `Monotone.abs_mul_ge`, `Monotone.abs_prod_ge` |

## tangent — nla_tangent_lemmas.cpp

| id | source | schema | Lean form | status |
|----|--------|--------|-----------|--------|
| T1 | line1 :101, line2 :113 | x = a → xy = a·y (const a); symmetric in y | `mul_comm`+subst, trivial | n/a — substitution at instantiation |
| T2 | plane :76 | (x−a)(y−b) > 0 → xy > ay + bx − ab; (x−a)(y−b) < 0 dual; 4 orientations via point placement | expand + `mul_pos`/`mul_neg_of...` | proven: `Tangent.plane_gt/lt/ge/le` |

## divisions — nla_divisions.cpp (real `/` and integer `div`)

| id | source | schema | Lean form | status |
|----|--------|--------|-----------|--------|
| D1 | :58 | y₁ ≥ y₂ > 0 ∧ 0 ≤ x₁ ≤ x₂ → x₁/y₁ ≤ x₂/y₂ | `div_le_div_of...` | proven: `Divisions.div_le_div_of_le_of_pos` |
| D2 | :72 | y₂ ≤ y₁ < 0 ∧ x₁ ≥ x₂ ≥ 0 → x₁/y₁ ≤ x₂/y₂ | dual | proven: `Divisions.div_le_div_of_neg_of_nonneg` |
| D3 | :86 | y₂ ≤ y₁ < 0 ∧ x₁ ≤ x₂ ≤ 0 → x₁/y₁ ≥ x₂/y₂ | dual | proven: `Divisions.div_ge_div_of_neg_of_nonpos` |
| D4 | :190 | y = yv ∧ x ≤ yv·div(xv,yv) + yv − 1 → div(x,y) ≤ div(xv,yv) | `Int.ediv` bound lemmas | proven: `Divisions.ediv_le_of_le` |
| D5 | :197 | y = yv ∧ x ≥ yv·div(xv,yv) → div(xv,yv) ≤ div(x,y) | `Int.ediv` bound lemmas | proven: `Divisions.le_ediv_of_ge` |

Note: Verus reaches this module through Euclidean div/mod on int; check which
of D1–D3 (real division) are reachable from Verus-emitted AIR at integration
time — likely only the idiv rows D4–D5 matter for tactus.

## monomial_bounds — monomial_bounds.cpp

| id | source | schema | Lean form | status |
|----|--------|--------|-----------|--------|
| MB1–2 | :113/:127 | m ∈ ∏ᵢ [loᵢ, hiᵢ] (interval product soundness); clause emitted when model value exits the range | interval arithmetic over ordered ring, `List` fold | proven: `Intervals.mem_intervalMul`, `Intervals.mem_intervalProd` |
| MB3 | :199 | p even ∧ U < 0 → v^p ≤ U infeasible (even powers are nonnegative) | `even_pow_nonneg` contradiction | proven: `MonomialBounds.even_pow_nonneg` |
| MB4 | :211/:221 | v^p ≤ U, r = U^(1/p) ∈ ℚ: p odd → v ≤ r; p even → −r ≤ v ∧ v ≤ r (each conjunct its own clause; strict variants when the range bound is open) | odd: `Odd.pow_le_pow_iff` monotone; even: `abs_le` ↔ `pow_le_pow` | proven: `MonomialBounds.le_of_odd_pow_le`, `abs_le_of_even_pow_le` |
| MB5 | :245 | v^p ≥ L, r = L^(1/p) ∈ ℚ: p odd → v ≥ r; p even (L ≥ 0) → v ≥ r ∨ v ≤ −r (genuinely disjunctive clause) | odd monotone; even via `le_abs` | proven: `MonomialBounds.ge_of_odd_pow_ge`, `ge_or_le_of_even_pow_ge` |
| MB6 | :383 | all factors fixed → m fixed (propagate fixed) | product of constants | n/a — instantiation-time subst + `norm_num` |

## module-level rules (not schema lists)

| id | source | rule | Lean discharge |
|----|--------|------|----------------|
| H1 | horner.cpp | interval evaluation of Horner forms is sound | proven per step: each Horner step is one `Intervals.mem_intervalAdd` + one `Intervals.mem_intervalMul`, chained at instantiation |
| G1 | nla_grobner.cpp | equality consequences in the ideal of hypothesis equalities | `linear_combination` / grind ring certificates |
| BR1 | nla_core add_bounds | integer branch: x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉ | trivially valid case split; omega handles leaves |
| PL1 | nla_core :1561 refine_pseudo_linear | all-but-one factor fixed → m = (∏ consts)·x | product substitution |

## exclusions and version notes

* `nla_powers.cpp` (x^y): unreachable from Verus-emitted AIR (no
  exponentiation primitive; vstd `pow` is an opaque recursive spec fn).
  Documented exclusion, revisit only if Verus adds a power primitive.
* `dioph_eq.cpp`: present in the 2026-02 checkout, absent from shipped Z3
  4.12.5. Not needed for 4.12.5 parity; add rows if verus-dev bumps Z3.
* nlsat is not in this table by design — it is the L2/L3 trace-checking story
  (DESIGN.md §2), not a lemma schema.

Additional note on integer bound tightening (`propagate_bound` :159): when
the bounded variable is integral, `v > q` strengthens to `v ≥ q+1` (integral
`q`) or `v ≥ ⌈q⌉`. This is LIA-valid rounding, subsumed by the omega leaf —
recorded here so the row inventory is complete, but it is not a nonlinear
schema.

## generator coverage audit (nla-05, 2026-07-24)

The table above is the "schema is proven" half of containment. This section
is the other half: does the **generator** (`Tactic/Saturate.lean`)
instantiate each reachable row at least as strongly as Z3's emission site?
Standard (parity directive): no divergence anywhere; Z3's schedulers only
select from the closure, so generator ⊇ emission site per row suffices.

Verified mechanism facts used below: omega case-splits on disjunctive
hypotheses (`Frontend.lean:410,640` via `Or.elim`); omega unfolds literal
powers to products (`Frontend.lean:218-224`), so `x^2` and a noted fact
about `x*x` share an atom; Z3 down-propagates m-bounds to factor bounds by
interval division incl. powers (`monomial_bounds.cpp:292,318`).

| row(s) | generator status |
|--------|------------------|
| B1 | covered by construction — `ring_nf at *` canonizes sign-flipped monomials to one atom (± a linear sign omega absorbs); stronger than Z3's emitted equation |
| B2, B3, B4, B10 | covered — sign lattice + zero rules, n-ary via postorder composition (nested-monomial noting) |
| B5 | **was a gap, fixed this slice** — `m = 0` provable with neither factor's zero known → note `a = 0 ∨ b = 0` (`mul_eq_zero.mp`); omega splits |
| B6 | covered in the premise-discharged direction (zero rule notes the consequent); indeterminate direction → class D |
| B7, B8, B9b | class D (conditional clauses); B8's sign-determined instances partially served by order/corner rows |
| B9, PL1, T1, MB6, O3-const | **was a gap, fixed this slice** — factor mined to a point (`lo = hi = c`) → note `a*b = c*b` / `a*b = a*c` (const-substitution; conclusion omega-linear) |
| O1 | covered when anchored — tangent at `(pivot, 0)` is exactly O1; the `0` anchor is mined from sign hypotheses *and from previously noted facts* (mineBounds runs in the evolving context); indeterminate-sign variants → class D |
| O2, O3-symbolic | **fixed (class C slice)** — pair phase scans hypotheses for comparisons (≤/</=, GE/GT swapped) between products sharing a factor, cancels via lattice sign (`sr_cancel_*`, all four `mul_comm` alignments); the specimen closes. Residuals: comparisons derivable but not hypothesis-present (oracle v1 territory, same as derived bounds), and `≠ 0`-only factor signs (class D) |
| O4 | covered for syntactically equal shared factors via the pair phase (ring_nf canonizes); Z3's `evars` ±-equivalences beyond that → class D residual |
| M1, M2 | covered at mined bounds via corner rows (evaluated literals = Z3's baked model consts); anchor-selection tightness → class E |
| T2 | covered at mined anchors, 4 orientations; model-anchor tightness → class E |
| D1–D3 | real division — unreachable from Verus AIR (int-only); standing exclusion, re-check at integration |
| D4, D5 | literal divisors: omega leaf handles `ediv`/`emod` natively (covered once div atoms are collected — boarded with multi-round); symbolic divisors → class C/D |
| MB1–2 | covered — corner rules, literal-folded exactly like Z3's `propagate_bound` (evaluated `q`, ±1 strict-int tightening on both sides) |
| MB3 | covered — `sr_pow_even_nonneg` unconditional |
| MB4, MB5 | **fixed (class C slice)** for k = 2 — `sr_sq_root_ub_hi/lo` (both conjuncts noted separately, as Z3 emits them) and the genuinely-disjunctive `sr_sq_root_lb` (omega splits); floor/ceil √ in meta, decide-certified. k ≥ 3 roots boarded with the k ≥ 3 envelopes |
| propagate_down (products) | **fixed (class C slice)** — `sr_down_{ub,lb}_{pos,neg}` + single-sided variants: exact interval division in meta (soundness rests on the decide-checked side conditions, so the β formula can only lose tightness), lattice unit-strengthening for strict-signed divisors, tightness gate mirroring `should_propagate_*`. Plus `sr_dsign_*`: divisor-sign quotients of the atom's sign, which the LIA leaf cannot derive. n-ary chains (inner atom fed by outer's bound) need the multi-round loop — postorder runs inner-first |
| squares (MB1-2/T2 for `x^2`) | **was a gap, fixed this slice** — pow monomials previously got sign rules only; now secant upper + per-anchor tangent lower at mined bounds (the convex envelope; McCormick for `a*b`, secant/tangent for `a^2`) |
| H1 | believed covered — per-monomial McCormick envelope + LIA leaf reproduces Horner interval brackets (Horner's factored forms don't survive `ring_nf` anyway); pinned by the Horner specimen test |
| G1 | out of scope for L1 — nla-07 Gröbner layer |
| BR1 | covered — omega leaf is LIA-complete over the atomized vocabulary |
| powers k ≥ 3 | **boarded** — envelope rules currently k = 2 only; Z3's interval pow is k-generic |

Gap classes:

* **Class C — down-propagation & pair rules** (O2/O3/O4, MB4/MB5,
  `propagate_down` for products): **done 2026-07-24** (see the fixed rows
  above). Residuals folded elsewhere: derived-not-present comparisons →
  oracle v1; ±-equivalences and `≠ 0` signs → class D; n-ary chains and
  k ≥ 3 → multi-round / boarded.
* **Class D — conditional clauses under indeterminate signs** (B6/B7/B8,
  O1-indeterminate): Z3 emits lazily model-guided disjunctive clauses; eager
  noting risks the min/max split lesson. Needs design (note clauses only for
  lattice-unknown factors; ties into multi-round and nla-06). Specimen:
  `(hx : x ≠ 0) (hy : y ≠ 0) : x*y ≠ 0`.
* **Class E — mined vs model anchors** (M/T tightness): DESIGN-discharge-
  oracle §2b / oracle v1 / nla-06.

## next actions

All emission sites are read, rowed, template-proven (nla-04), and now
generator-audited (above). Open parity work, in order: class C
(down-propagation + pair rules), class D design, multi-round loop, div/mod
collection, k ≥ 3 envelopes, oracle v1.
