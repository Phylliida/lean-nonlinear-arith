# BOARD — lean-nonlinear-arith

Risk-first ordering: nla-01..03 are the derisk spikes and come before any
infrastructure investment. Status: `todo` / `active` / `done` / `blocked` /
`dropped`. See DESIGN.md for architecture and the risk register.

## Derisk spikes (do first, in any order, all cheap relative to what they retire)

- **nla-00** `done` Repo + Lake scaffolding, mathlib v4.25.0 pin, library layout.
- **nla-01** `done` **S1 statement spike.** `Projection/S1Statement.lean`
  elaborates clean, first pass: psc chains defined as explicit Sylvester-minor
  determinants (mathlib has `resultant`/`sylvester` but no subresultants — ours
  to build), `ParamPoly k = Polynomial (MvPolynomial (Fin k) ℝ)`, conclusion
  packaged as a `Delineation` structure (continuous strictly-ordered root
  functions, constant membership). No mathlib gaps blocking the statement.
  Statement may still evolve during the nla-11 proof campaign.
- **nla-02** `done` **Root-counting spike (S2-lite).** `RootCounting/Spike.lean`,
  all proven, no sorries: generic sign-invariance-from-rootlessness (IVT
  contrapositive — the checker's cell-sign workhorse), unique-root isolation for
  a concrete polynomial (IVT + `strictMonoOn_of_deriv_pos`), and the Rolle-chain
  bound composing (`Polynomial.card_roots_le_derivative` exists in mathlib!).
  Verdict so far: per-instance counting looks viable without general Sturm;
  final call after higher-degree census specimens (keep nla-10 conditional).
- **nla-03** `done` (descoped by design decision 2026-07-24). The project is
  proof-first: we cover all cases by porting the equivalent of everything Z3
  does and proving containment — coverage never depends on which goal shapes
  are common, and build order follows Z3's own pipeline architecture, so the
  census shape distribution is not an input to anything. Kept as record only:
  `Corpus/Rational.lean` with 3 proven specimens as plain regression tests;
  `data/census-*.txt` as the historical experiment log. Dropped: mass
  transcription, baseline tables, second-crate census, v0 heuristic tactic.
- **nla-20** `done` (2026-07-24, RULES.md — 39 emission sites rowed, all
  proven or n/a-with-reason) **Rule-correspondence spec.** The early artifact the
  containment proof actually needs: a source-referenced table mapping every
  Z3 nla generator to its Lean lemma family — nla_basics_lemmas.cpp schemas,
  order, monotonicity, tangent, divisions, monomial bounds, one row per rule,
  with the C++ provenance and the corresponding lemma statement. This document
  is the "Z3 ⊆ calculus" half of the structural argument (checked by reading,
  not running) and the fidelity contract nla-04/05 are built against.

## L1 — saturation layer

- **nla-04** `done` (2026-07-24) Template lemma library:
  `Templates/{Basics,Order,Monotone,Tangent,Divisions,Intervals}.lean`, all
  sorry-free; RULES.md fully resolved (27 rows proven or n/a-with-reason,
  zero todo). L1's mathematical content is finished — nla-05..07 are
  metaprogramming over a fixed lemma kit.
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
- **nla-06** `todo` Linear leaf. **v0 decision: omega IS the leaf** — after
  monomial abstraction (each monomial -> fresh variable) the per-round closure
  check is a linear-ℤ problem, exactly omega's domain; no simplex needed until
  we want *models* to guide generation (Z3-style model-based lemma selection).
  v1 (only if blind saturation proves too slow on real corpora): untrusted
  exact-rational simplex (~300 lines meta) for models + Farkas certificates
  via linear_combination. Base to extend: `Tactic/Oracle.lean` (2026-07-25)
  already parses the atomized constraint system and propagates bounds —
  the simplex adds a feasible point over the same structure. Consumers
  waiting on the model: clause-phase relevance filtering, model-anchored
  D4/D5/M/T tightness, derived product-pair comparisons (O2/O3 residual).
  Documented divergence to close here (2026-07-26): Z3's column bounds
  can come from simplex TABLEAU rows — linear combinations of the
  original constraints — which row-interval propagation over the original
  rows cannot reach; the simplex port restores that strength (and its
  octagon-term bounds then feed `collect_equivs` at full Z3 strength).
- **nla-07** `done` (2026-07-25) Gröbner layer via grind's ring engine, per
  the DESIGN §L1 decision (no PDD port). ℤ-equality goals: sandboxed fast
  path before saturation (Z3 stage-3 scheduling). All shapes: a second
  chance after the eager leaf fails, ahead of the clause tiers (their
  sign-unknown case-split cost dwarfs a failed ring probe — probe-confirmed
  heartbeat blowout the other way around). `≤`/`≥` goals additionally try
  the `le_of_eq`-strengthened form: grind's ring module derives ideal
  equalities but its cutsat bridge never consumes them (probe-confirmed on
  the equality-core inequality specimen). Attempts heartbeat-capped at half
  the remaining budget (`Core.Context` override + `tryCatchRuntimeEx`).
  Census rows division_699 + cauchy_schwarz_233 close push-button; 112
  examples green.
- **nla-07b** `todo` **Gröbner→saturation propagation.** Z3's
  `propagate_eqs`/`propagate_fixed`/`propagate_linear_equations` feed
  Gröbner-DERIVED equalities back into the LRA solver, where they become
  anchors/pins for the order/tangent/interval machinery on inequality
  goals — a composition the goal-directed grind reuse cannot replicate
  (grind exposes no basis API; probe: it derives `e*a - c*d = 0` in its
  basis yet fails the ≤ goal). Port: small meta-Buchberger over ℚ[atoms]
  with cofactor tracking (untrusted, oracle-style), noting derived
  equalities whose monomials all live in the collected atom vocabulary,
  each certified by `linear_combination` with delaborated cofactors (or
  discharged by a grind call on the equality subgoal). Pairs naturally
  with the nla-06 simplex work.

## Standing directive: source-fidelity over empirical confirmation

(Danielle, 2026-07-26) Where we lean on an *equivalent* engine instead of
porting Z3's ("grind's Buchberger ⊇ Z3's throttled PDD, checked by the
nla-16 harness"; "ring_nf ≈ emonics"), prefer making it THE SAME — we
have the source code. Consequences: nla-07b's meta-Buchberger should be a
faithful port of the `nla_grobner` pipeline (its five consumers:
conflict, propagate_fixed, propagate_factorization, propagate_gcd_test,
propagate_quotients), after which grind demotes to an auxiliary layer and
containment no longer rests on a reading of grind's internals; nla-21's
shared-atom-space design should reconsider the emonics port likewise.
The octagon `collect_equivs` port (2026-07-26) is the template: read the
site, match the mechanism, keep any strict superset only where the
containment direction is free.

## L1 hardening (from the 2026-07-25 code review; directives from Danielle)

- **nla-21** `todo` **Shared atom space for noted facts.** The right fix for
  the orientation-bug class (review fix e104567 covers only `mul_comm` of
  the div defining equation): meta-built composites in noted conclusions
  can land on different omega atoms than ring_nf's canonization of the same
  user-written term (instance spellings remain even after the orientation
  fix). Design constraints mapped during review: (a) `ring_nf at *` after
  noting invalidates positive discharge-cache entries — their proof terms
  reference hypothesis fvars that ring_nf replaces; (b) per-fact
  `ring_nf at h` inside `noteFact` is safe for the cache (user fvars
  untouched) and dedup keys (computed pre-normalization from the built
  conclusion), but then the appended `ms` product spelling must ALSO be the
  canonical form or `mineBounds`' syntactic lookups miss — needs a meta
  entry point to ring_nf-normalize an `Expr` (investigate
  `Mathlib.Tactic.RingNF` internals) applied consistently to noted facts
  AND collected/appended atom spellings; (c) the clause phase instantiates
  from pre-canonical `ms` exprs and must go through the same normalization.
  Scope: noting path + collection + clause phase, one design.
- **nla-22** `todo` **Dependency work-queues, Z3-identical.** Replace the
  brute-force fixpoint re-run (+54% tactic calls on the stress goal for
  confirmation) with Z3's scheduling: track which facts changed per round
  and re-run a generator for monomial m only when one of m's inputs (factor
  bounds, factor signs, atom bounds) gained a fact. Directive: the goal is
  to be IDENTICAL to Z3's behavior, so port the todo-list structure from
  nla_core/monomial_bounds rather than inventing an equivalent.
- **nla-24** `active` **Kernel/oracle correctness lemmas** (2026-07-26).
  Proving the untrusted computations right where it is cheap, per
  Danielle's review directives. Done: the oracle tighten formulas are
  fully characterized (`cdivPos_le_iff` / `le_fdiv_iff_mul_le` in
  Oracle.lean — iff = soundness + tightness; the ub step recomputed in
  positive-divisor form to match the lemma verbatim); `nonRootSplit`'s
  try count made provably sufficient (counting argument in the
  docstring). Remaining candidates, roughly by value: `propagate`'s
  sup-accumulation loop (the residual trust in the oracle),
  `QPoly.psc = S1Statement.psc` bridge (the kernel's numbers ARE the
  spec's numbers — currently by construction-mirroring, provable as a
  determinant identity), Yun reconstruction (`∏ aᵢ^i = monic p` — pinned
  by #guard on specimens today), Sturm correctness (= S2/nla-10
  territory, don't duplicate).
- **nla-23** `todo` **q-formula optimality proofs.** The D4/D5 quotient
  candidates and down-prop β formulas are hand-derived Euclidean interval
  reasoning; soundness rides on templates (wrong formula = lost tightness
  only). Prove them RIGHT once and for all in Lean: per formula, an
  attainment lemma (`∃ x y` in the mined box with `x / y = q`) certifies
  the emitted bound is the exact interval optimum — stronger than Z3,
  which never proves its own tightness. Same treatment for corner-fold
  min/max and the k-th-root exactness window.

## Kernel + kit

- **nla-08** `done` (2026-07-25) Computational ℚ[x] kernel (untrusted),
  `Kernel/QPoly.lean`: dense ops, exact divRem, monic-Euclid gcd,
  square-free part + Yun, Sturm chains + root counting, Cauchy bound;
  psc/resultant chains computed as determinants of the EXACT Sylvester
  submatrices from `Projection/S1Statement.lean` (spec-faithful — the
  kernel's numbers are definitionally the spec's numbers). **Perf derisk
  cleared decisively**: sturm/wilkinson-40 14ms, deg-16×16 psc chains
  ~70ms, quadratic-lane degrees (≤8) sub-ms — determinant route stands,
  subresultant-PRS fast path only if the deep tail ever demands it.
  Benchmark honesty lesson recorded in `Kernel/QPolyBench.lean`: pure
  computations must be forced (unless-throw) before the closing
  timestamp, else the compiler defers them past it and every phase reads
  0ms.
- **nla-09** `done` (2026-07-26) Real algebraic numbers as (poly, isolating
  interval). **Computational half (2026-07-25)**, `Kernel/Roots.lean`:
  Sturm-bisection isolation (disjoint rational open intervals, non-root
  endpoints by split-nudging, square-free internally), interval
  refinement, Tarski-query sign determination at an isolated root
  (generalized chain `f, f'·g`; single-root TaQ = sign, incl. the 0 case).
  **Trusted bridge (2026-07-26)**, `Certificates/{Defs,Sound}.lean` +
  `Kernel/CertGen.lean`: certificate checkers as Bool programs over
  **unnormalized `Int × Int` fractions** (probe: kernel `decide` cannot
  whnf `Rat.add` — normalization sticks — while gcd-free cross-mult pair
  arithmetic reduces GMP-fast; coefficients ℤ-scaled by the kernel), so a
  claim enters a proof as `check*_sound (by decide)` with an O(1) proof
  term. Certificate language: `lip` (MVT Lipschitz-margin leaf:
  `(absZ p')(max |a| |b|) · (b−a)/2 < |p(mid)|`) + `split` — complete for
  root-free closed intervals by compactness; no monotonicity node needed
  yet. Trusted claims: `checkNoRoot_sound`, `checkUniqueRoot_sound`
  (∃!-root via IVT both orientations + strict mono/anti from
  sign-invariant derivative — nla-02's lemmas doing exactly their planned
  job), `checkPosOn_sound`/`checkNegOn_sound` (cell signs). Generation:
  refine-until-margin bisection; unique-root claims shrink the isolating
  interval until the derivative is root-free on the *closed* interval
  (reachable: square-free ⇒ simple root); `certify*` re-verify through the
  trusted checker before returning (`isSome` ⇒ the `decide` succeeds).
  Tests: kernel-`decide` end-to-end (√2 ∃!, cubic sign cell, generator's
  own x²+1 cert re-checked, ℝ-form massage example = the future tactic's
  emission shape), negative probes, square-free path `(x²−2)²`, √3 from
  `(x²−2)(x²−3)`. Full file elab ~10s incl. all decides.
- **nla-10** `todo` General Sturm theory — only if nla-02 says per-instance
  Rolle-chains don't suffice. AFP Sturm_Sequences as the map. Upstream-worthy.
- **nla-11** `todo` **S1 proof campaign.** The long pole; two independent
  tracks that join at final assembly:
  * *algebra track*: 11a resultant vanishing (Res(f,g)=0 <-> not coprime, via
    Sylvester kernel <-> Bezout; then common root over ℂ, descend to ℝ) —
    upstream-worthy on its own; 11b psc <-> gcd-degree correspondence
    (subresultant theory core, the biggest algebra piece);
  * *analysis track*: 11c continuous dependence of roots on parameters at
    constant degree (via Rouché in mathlib's complex analysis, or elementary
    compactness); 11d topological glue: constant count + continuity +
    connectedness => ordered continuous root functions (the Delineation).
- **nla-19** `todo` **Quadratic-complete checker (S1-free).** Sequencing
  insight: nlsat lowers root conditions to Thom sign encodings at degree <= 2
  (`mk_quadratic_root`), and the nla-02 lemmas (sign-from-rootlessness, IVT
  isolation) already discharge those plus cell-sign steps. A checker restricted
  to traces whose projection steps stay at degree <= 2 per variable needs NO
  S1 — and Verus goals are overwhelmingly per-variable degree <= 2. Build this
  first; full S1 (nla-11) only unlocks the deep tail. Converts the capstone
  from a cliff into a ramp.

## L2/L3 — nlsat

- **nla-12** `active` (lane opened 2026-07-26; slice plan + module map +
  trace language + discharge map in **DESIGN-nlsat-quadratic.md**) nlsat
  search port (classic path of nlsat_solver.cpp / nlsat_explain.cpp; no
  levelwise). Emits traces in the 5-shape language (DESIGN.md section
  2/L3) + integer branch splits. The search is generic in degree; the
  quadratic fragment (deg ≤ 2 per top variable) is enforced at
  explain/check time — S1-free per the one-identity insight
  (`4a·p = (2ay+b)² − disc`). Done so far: **S3 Thom kit**
  (`Templates/Quadratic.lean`, sorry-free: sign dictionary iffs both
  lead signs, definite disc≤0 cases, the 4-lemma point-vs-root-interval
  ordering family + roots-order; mirrors mk_quadratic_root
  nlsat_explain.cpp:886) and **mini-anum** (`Kernel/RAlg.lean` +
  tests: rat|root representation, compare with gcd common-root fast
  path + fueled refinement separation, sign / signOfPolyAt via Tarski,
  ratBetween for witness picking; mkRoot normalizes linear→rational for
  Z3's rational-preference parity). Next slices: nla-12a Types/Trace +
  IntervalSet (justification-preserving mk_union per
  nlsat_interval_set.cpp), 12b Evaluator, 12c Solver loop, 12d Explain
  (fragment-checked), then nla-19a Check.lean v0.
- **nla-13** `todo` Trace checker: discharge shapes 4/5 by per-instance ring,
  shape 2 by degree dispatch (ineq / Thom / nla-09), shapes 1/3 by S1 + S2.
- **nla-14** `todo` Front-end tactic `nonlinear_arith`: Int -> Real relaxation,
  L1 then L2/L3 layering, hypothesis selection matching Verus query shape
  (context-free: only stated requires).

## Integration

- **nla-15** `todo` tactus closer wiring: emit `nonlinear_arith` for
  `by(nonlinear_arith)` sites. Toolchain already aligned (tactus/lean-project
  pins lean+mathlib v4.25.0, identical to ours; integration is a require line).
- **nla-16** `todo` Parity harness: run the full workspace nonlinear corpus
  through the tactic; compare against Z3 site-for-site; census-style report.
  Acceptance: no site that Z3 closes and we don't.

## Milestone ladder (proof-first)

- **M1** rule-correspondence spec + template lemma library built against it
  (nla-20, nla-04).
- **M2** L1 complete — bookkeeping, saturation loop, omega leaf, Gröbner
  layer; correspondence table fully covered (nla-05..07).
- **M3** quadratic-complete nlsat — degree-<=2 search + S1-free checker
  (nla-08, nla-09, nla-12 restricted, nla-19).
- **M4** S1 campaign, algebra + analysis tracks in parallel (nla-11, nla-10
  if needed).
- **M5** full checker + the containment argument written up end to end:
  per-rule fidelity (nla-20 table) + saturation completeness + RCF trace
  checking (nla-13, nla-14).
- **M6** tactus integration, then the single end-stage empirical pass:
  workspace parity harness as confirmation, not guide (nla-15, nla-16).

The guarantee is delivered by M5 on paper + kernel; M6's harness exists to
confirm budgets/performance (the one declared-empirical residue) and to catch
spec-fidelity mistakes in the correspondence table, not to define coverage.
