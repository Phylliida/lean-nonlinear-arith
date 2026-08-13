- **nla-05** `done` (2026-07-25; hardening follow-ons live in nla-21..23)
  Monomial bookkeeping (emonics port) + generator loop.
  **Slice 1 done (2026-07-24):** `Tactic/Saturate.lean` — `nla_saturate` v0
  proves the architecture end-to-end on 11 regression tests
  (`Tactic/SaturateTests.lean`): postorder monomial collection over ℤ,
  sign/zero/square generation from a fixed `sr_*` rule vocabulary, premises
  discharged by `assumption <|> omega` *inside the evolving goal context*
  (nested monomials feed outer premises), revert/generalize/intros
  abstraction, omega leaf. **Slice 2 done (same day):** mined-constant
  order/interval generation — `mineBounds` extracts literal bounds from
  hypotheses (strict ℤ bounds tightened by one), generators instantiate
  `sr_lb_mul`/`sr_ub_mul`/`sr_ub_neg_mul` plus the full corner-product
  Intervals templates; 17 tests green, ~300ms/goal. **Slices 3+4 done (same day):** ring_nf
  normalization front-end (doubles as commutative canonization — obsoletes
  most of the emonics port) + power monomials with decide-discharged
  parity side conditions + tangent-plane generation anchored at mined
  constants (four orientations, linear conclusions; closes the classic
  `1 ≤ x → 1 ≤ y → x + y ≤ xy + 1`). 31 tests green after
  the 2026-07-24 review round (loose-bvar crash fixed, redundant
  abstraction step removed — omega atomizes natively, assumption pinned
  in tests; sr_tan_* rerouted through Templates.Tangent). **Slice 5 done
  (2026-07-24 pm): discharge oracle items 1 + 2a + v0.5** — canonical
  sandboxed tryDischarge (env kept for omega's aux constants,
  `mkExpectedTypeHint` for defeq-typed extractions), memoized discharge
  cache (negatives dropped per noting round), per-factor sign lattice
  (≤3 probes, rules read it with zero tactic calls), literal-vs-literal
  fast path in meta code, mineBounds consumeMData/instantiateMVars
  hygiene, and corner min/max folded to literals at generation time (the
  dominant bug: noted min/max facts made the omega leaf case-split
  exponentially — 168s → 76ms). Stress goal (8 monomials, lb+ub per
  factor): baseline heartbeat-timeout → ~2.1s (32 tactic calls, 162
  cache hits); pinned as a regression test, 32 tests green.
  `nla_saturate_stats` reports phase timings + oracle counters. See
  DESIGN-discharge-oracle.md §Outcome. **Slice 8 done (2026-07-24 eve):
  class D — failure-gated conditional clauses.** The leaf runs once on
  the eager layer; on failure the tactic rolls back, notes the clause
  vocabulary, and retries — Z3's lazy model-guided emission, model-free.
  Clauses: 4 sign (`sr_cl_pp/nn/pn/np`), 2 zero + B5 (`sr_cl_zl/zr/b5`),
  B7/B8 in natAbs form (omega-native, clause-phase-only since natAbs
  case-splits), 8 O1 pivot clauses. Gates: lattice-unknown factor
  required; B7/B8 need a discharged ≠0; O1 a discharged pivot. Specimen
  `x≠0 ∧ y≠0 → x*y≠0` closes; 53 tests green; stress stays on the eager
  path (56 calls, no retry — zero clause cost for green goals).
  ⚠ timings this eve under load-88 (uptime lesson) — call counts are the
  stable metric. **Slice 7 done (2026-07-24 pm):
  class C — down-propagation + pair rules.** O2/O3 cancellation via a
  zero-call syntactic pair scan (all four mul_comm alignments, GE/GT
  normalized with expected-type hints) + lattice signs; product
  down-propagation `sr_down_*` by exact interval division in meta
  (decide-certified side conditions carry soundness, β formulas only
  affect tightness; single- and two-sided, pos/neg divisors, lattice
  unit-strengthening, Z3-style tightness gate); down-sign quotients
  `sr_dsign_*` (nonlinear, invisible to the leaf); MB4/MB5 k=2 integer
  roots incl. the genuinely-disjunctive MB5 clause. 11 new tests, 47
  green; stress 56 calls / ~3.5s. RULES audit rows flipped to fixed;
  residuals: derived-not-present comparisons → oracle v1, ±-equiv and
  ≠0 signs → class D, n-ary down-chains → multi-round. **Slice 6 done
  (2026-07-24 pm): generator parity audit** (PARITY DIRECTIVE: identical behavior to Z3,
  no divergence anywhere — every RULES row checked generator-side, table
  in RULES.md §generator coverage audit). Three gaps found and fixed
  same-slice: B5 zero-product split (disjunctive noting, omega
  `Or.elim`-splits), const-substitution B9/PL1/T1/MB6 (factor mined to a
  point, other factor unbounded), square envelopes (secant + tangent for
  `x^2` — pow monomials previously had NO mined-bound rules; closes the
  Horner/H1 specimen). 36 tests green. **Slice 9 done (2026-07-25):
  multi-round saturation.** Bounded rounds to fixpoint (default 3,
  `nla_saturate n` overrides), fixpoint detected by a noted-conclusion
  dedup set seeded with hypothesis types (`noteFact` skips
  already-present conclusions and reports novelty; `generate` /
  `generatePairs` return the progress signal). Parity: the single
  sequential pass was Gauss-Seidel — order-dependent along the
  ring_nf-determined context order — while Z3's final-check loop
  saturates order-independently; this closes the "single round vs
  saturation loop" divergence and delivers the n-ary down-prop chains.
  Specimen (confirmed failing single-round through both clause tiers):
  order-reversed chain where the tangent target `x*w` precedes the
  down-prop source `x*y`, so round 2 must re-anchor the tangent at the
  derived `x ≤ 5`. Notable probe finding en route: within-pass
  sequential noting + the clause tiers' post-noting re-mining already
  close most chains (O1 pivot clauses act as a disjunctive round 2 for
  single-pivot chains) — only order-reversed corner/tangent-anchoring
  chains genuinely need rounds. 64 tests green; stress goal stays
  eager-path, 56 → 86 tactic calls (round-2 re-probe of dropped
  negative cache entries = the fixpoint-confirmation cost).
  **Slice 10 done (2026-07-25): div/mod collection.** Symbolic-divisor
  `ediv`/`emod` pairs collected alongside monomials (literal divisors
  are omega-native — probed: omega atomizes symbolic-divisor terms
  rather than erroring, so no pre-generalization needed). Per pair:
  defining equation `y·(x/y) + x%y = x` (its product joins the monomial
  set up front, so corners/tangents/down-prop reason about the
  quotient), sign-gated Euclidean mod range (pos, neg via `Int.emod_neg`
  flip, and a discharged-`≠0` fallback for the lower bound),
  const-substitution at point-mined divisors (D4/D5's `y = yv` anchor
  made omega-native, incl. the lattice-zero degenerate case), and D4/D5
  interval-quotient bounds via the `Templates.Divisions` lemmas with
  meta-computed `q` and omega-discharged premises (literal `q` keeps
  them linear; wrong `q` only fails to note — sr_down-style safety by
  construction). Div pairs generate before the monomial loop (their
  facts feed the sign lattice; the reverse dependency is caught by the
  next round). Soundness probe: `0 ≤ x % y` with no `y ≠ 0` hypothesis
  correctly fails (the passing test's unused-variable lint is a linter
  false positive — it only tracks syntactic uses). 81 examples green;
  stress goal untouched (no div atoms → zero cost).
  **Slice 11 done (2026-07-25): k ≥ 3 power envelopes + roots.**
  Interval-pow envelopes (odd via `Odd.pow_le_pow`, even via
  `M = max(|lo|,|hi|)` and signed lb variants) + MB4/MB5 roots at
  general exponents (contrapositive `u < (r+1)^p` lemmas mirroring the
  k = 2 pattern; meta integer k-th roots by binary search, odd roots
  over all of ℤ — negative radicands included). k = 2 keeps its tighter
  secant/tangent path. `sr_pow_root_lb_even` needed no `1 ≤ r` premise
  (tautological disjunction for r ≤ 0; contradiction branch derives
  r ≥ 1 itself). 98 examples green. **L1 generator parity is COMPLETE**
  — every RULES row is fixed, n/a-with-reason, or routed to oracle v1
  (derived bounds, O4 ±-equiv, clause relevance, model-anchored
  tightness). **Oracle v1 done (2026-07-25, slices A+B,
  `Tactic/Oracle.lean`):** (A) untrusted integer bound propagation over
  the atomized ℤ-linear hypotheses (`lp_bound_propagator` analogue,
  all-Int floor/ceil tightening, capped fixpoint) — derived tightest
  bounds join every mined-anchor set, purely additive, every suggestion
  omega-discharged before use; (B) O4 ±-equivalences via a parity
  union-find over unit ±-equalities (evars analogue) — eager `q = ±p`
  bridges for fully-equivalent mul/pow pairs (emonics canonization),
  model-free `generate_mon_ol` transfer clauses for one-equiv-factor
  pairs in clause tier 2. 10 probe-confirmed specimens, 108 examples
  green, stress unchanged (86 calls; oracle overhead unmeasurable in a
  same-load A/B). Remaining oracle work needs the *model* (nla-06):
  exact-rational simplex feasible point for clause relevance,
  model-anchored D4/D5/M/T anchor tightness, and derived product-pair
  comparisons. Next: nla-07 Gröbner.
  Original design sketch (2026-07-24):
  * *atom map*: `Expr ↦ atom id` for maximal non-arithmetic subterms; monomial
    = sorted multiset of atom ids + sign, canonized like `emonics.cpp`;
  * *state*: hypothesis set as linear atoms over the monomial-extended
    vocabulary + the defining equation per monomial variable;
  * *round*: each generator scans monomials, instantiates its RULES row
    (Lean lemma application via `mkAppM`, constants from hypotheses — NOT
    from a model in v0), adds conclusions as new hyps with proof terms;
  * *leaf*: after each round, try `omega` on the abstracted goal; success ⇒
    done, failure ⇒ next round; fixed generator order, no throttling,
    bounded rounds (default small; the containment statement is
    per-round-count, mirroring Z3's stratification);
  * *determinism*: no randomization, no model dependence in v0 — strictly
    more instances than any Z3 schedule at equal depth.
