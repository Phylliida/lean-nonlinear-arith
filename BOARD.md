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

## nla-25 `partial` — L2 kernel correctness upgrades (directives from Danielle, 2026-07-26)

**Status 2026-07-26 eve:** 25.1 resolved-by-removal (the gcd fast test
is gone — nla-26.3's `am::compare` port decides different-poly equality
via Sturm–Tarski `V == 0`; remaining counting trust = nla-10 as
before). 25.3 test pins landed and **caught a real sign bug** — a
`(−1)^{degF·d}` parity factor in `resultantElim` wrong for the
documented `Res_x(f,q)` orientation, invisible in the quadratic lane
(`d = 2` keeps the exponent even), exposed by the first `d = 3` pin and
removed. 25.5 differential test landed (~10k union checks vs the
membership oracle + justification provenance). **25.4 DONE 2026-07-26
(279680c, `Nlsat/TypesOrder.lean`):** `Monomial.cmp` proven a linear
order (refl / eq-iff-list-equality / swap / lt+gt-trans), `Canon`
predicates formalize the Types.lean storage invariants, preservation
proven through `Monomial.mul` and `MPoly.add/neg/sub/smulTerm/mul`;
keystone `cmp_mul_left` (`cmp (mul k m) (mul k n) = cmp m n`, an order
*equality*) via the dense exponent-vector characterization
(`go_eq_dense` + `degreeIn_mul` + `Nat.compare` translation-invariance)
— review correction: z3 does NOT rely on this (products are unsorted
`som_buffer` accumulation, `m_lex_sorted` only ever set by an explicit
`lex_sort`); the theorem discharges OUR eager representation's skipped
re-sort in `smulTerm`. Residual (out
of scope, note for later): `substRat`/`ofQPoly`/`coeffsIn` canonicity
not yet stated. **Still open:** proof-layer items only (25.2 = nla-10,
25.3's semantic layer = nla-11a).

From the fresh-context confidence audit + Danielle's review: fix
correctly AND prove where feasible (documented now, scheduled later —
"none of this needs to happen now… but I do want to fix eventually").
Scale flags are honest estimates.

1. **`RAlg.compareCore` gcd-equality endpoint-roots** — fix by
   `nonRootSplit`-style nudging of `lo`/`hi` off roots of `g` before
   counting; endpoint-root test battery. *Proof (Danielle: "ideally"):*
   layered — the cheap half ("a shared root of both polys inside both
   open isolating intervals ⇒ the numbers are equal") is provable NOW
   from root-uniqueness, no Sturm needed; the counting half ("Sturm says
   ≥ 1 root in the open overlap" is truthful) is nla-10 territory.
   [quick fix + cheap-half proof; counting proof gated on nla-10]
2. **`CertGen.rootFreeOn` Sturm conventions** — *prove* (Danielle:
   "worth trying"). This IS the Sturm correctness theorem = **nla-10
   revival** (AFP Sturm_Sequences as the map; upstream-worthy; a real
   multi-session subproject). Note the pragmatic layer that already
   exists: rootFreeOn is only a fast pre-check — the derivative
   root-freeness it gates gets re-certified by `genNoRoot` +
   `checkNoRoot` anyway, so its correctness affects completeness, not
   soundness. [subproject: nla-10]
3. **`detMPoly` / `resultantElim` correctness** — *proof not just tests*
   (Danielle). Two layers: (a) det-of-Laplace-expansion = spec
   determinant [medium, self-contained]; (b) the semantic property the
   call sites consume — common solutions survive elimination — is
   resultant theory = the **nla-11a orbit** (already boarded as the
   algebra track; this gives it a second consumer). Meanwhile add the
   cube-root ≥ 3×3 test pin (`Res_x(y − x, x³ − 2) = y³ − 2`). [test
   now-ish; proofs medium / nla-11a]
4. **MPoly order property theorems** (Danielle: yes) —
   totality/transitivity/antisymmetry of `Monomial.cmp` + canonical-form
   preservation through `add`/`mul`. Pure list induction. [cheap-medium,
   one session] **DONE 2026-07-26 eve, 279680c — see status above.**
5. **`mkUnion` differential test** (Danielle: yes) — random small sets,
   rational probes vs the "in s1 or s2" membership oracle +
   justification validity. [cheap]

## nla-26 `done` (2026-07-26 eve) — fidelity hardening: divergence elimination (Danielle, 2026-07-26)

**ARC COMPLETE**, commits 4429381..d429841. What landed, per item:
1. `Kernel/Mpbq.lean` — faithful `mpbq` port (renamed from Dyadic:
   mathlib ships a root-level `Dyadic` that captured name resolution).
   Surface = the `bqm()` census of algebraic_numbers/upolynomial;
   declared non-ports: `root_lower/upper` (radical constructor),
   `approx/approx_div` (no call sites; `basic_interval` is exact).
   Threaded through: `isolateRootsD` (integer initial bound; the
   bisection engine is dyadic-closed so it's shared, not duplicated),
   `RAlg.root` endpoints, `MpbqI` = `mpbqi` interval port in AnumEval
   (with 26.2's ℤ coefficients the evaluator path is rounding-free,
   exactly Z3's shape — `eval_sign_at` reading: rationals are
   substituted away, `SASSERT(!v.is_basic())`).
2. ℤ coefficients + Z3 monomial orders in `Nlsat/Types.lean`
   (`lexCompare` :625 = canonical storage order, the manager's only
   sorted form; `gradedLexCompare` :710 = leading-monomial max-scan
   order, storage-independent). `substRat` = denominator-clearing
   positive scaling (z3 `substitute`); `resultantElim` internals on a
   parallel ℚ-term copy, ℤ-scaled back.
3. Unfueled `compare` = 1:1 `am::compare`/`compare_core` ladder
   (disjointness / same-poly / magnitude equalization with
   became-basic re-dispatch / precision-10 workaround / Sturm–Tarski).
   Gcd fast test retired. `mkRoot` gained `am::normalize`
   zero-straddle normalization (new cell invariant: 0 never strictly
   inside).
4. `am::select` port (`separate` + 4-shape `select_small_core`) +
   `int_gt`/`int_lt` (`ceil(upper)`/`⌊v⌋−1` semantics — pick pins
   updated) wired into `pickInComplement`; `ratBetween` deleted.
5. Rationality discovery on refine (`refine_core` midpoint-zero test
   first; `refine1`/`refineUntilPrec` convert to basic on exact hits).
6. Binary magnitude/precision gating: `refineToPrecD` on `lt_1div2k`,
   `intervalMagnitude` (imp::magnitude verbatim), `minMagnitude = −16`,
   `RAlg.magnitude` for the 12b-ii evaluator gate.
7. Pick determinism kept (confirmed non-divergence).
Remaining declared divergences: Sturm-vs-Descartes isolation engine
(nla-08), kernel `QPoly` ℚ[x] vs ℤ upolynomial (bridged at `ofQPoly`),
root-represented rationals in the shared-endpoint preference,
no factorization (`m_minimal` always false).

Original item list (all done; anchors kept for reference):

1. **Dyadic (`mpbq`) interval endpoints** — "Rat seems sus, investigate
   doing it the same." Port binary rationals (`num · 2^{−k}`) as
   endpoint type + the rounding entry points `mpbqi` evaluation uses
   (rational coefficients round outward under a precision parameter);
   this is the KEYSTONE — it also makes 26.6 magnitude and 26.4 select
   natural. [medium]
2. **ℤ coefficients + Z3's monomial order** — "could we do their
   order?" Port `polynomial.cpp` ordering (`lex_compare` :625,
   `graded_lex_compare` :710 — read which one the manager actually keys
   monomial storage on) and integer-coefficient polys with Z3's
   normalization. Refactor of `Nlsat/Types.lean`. [medium]
3. **Unfueled `compare`** — "worries me to not be the same." Read
   Z3's `am.compare` mechanism (refine-until-disjoint + its exact
   equality detection) and port it 1:1, dropping our fuel/`.eq`-default.
   Interacts with 25.1. [small-medium after 25.1]
4. **`am.select` port** — "prefer Z3's way": dyadic
   smallest-denominator selection in gaps, replacing `ratBetween` in
   `pickInComplement`. Natural after 26.1. [small]
5. **Rationality discovery on refine** — "seems wrong, match Z3." Port
   `refine_core` (`algebraic_numbers.cpp:929`; became-basic sites :251,
   :306): bisection tests the midpoint sign and a zero midpoint
   normalizes the cell to a rational. Root cause of our divergence:
   `RAlg.refine1` delegates to `refineInterval`, whose `nonRootSplit`
   deliberately dodges root midpoints (right for isolation, wrong for
   value refinement). Fix shape: value-refinement path tests the
   midpoint root FIRST (`eval p m == 0 → .rat m` — the unique root is
   found exactly), then falls back to isolation-style splitting. Also
   revisit `mkRoot` (currently normalizes only linear). [small]
6. **Magnitude gating** — "do what Z3 does": binary magnitudes over
   dyadic endpoints (exponent arithmetic), replacing the Rat width
   threshold. Rides on 26.1. [small after 26.1]
7. **`pick_in_complement` determinism** — Danielle: keep deterministic
   (randomize = false path) — CONFIRMED, not a divergence to fix.
   nla-16's parity harness measures whether it costs coverage vs stock
   Z3 anywhere.

## nla-27 `done` (2026-07-28) — univariate ℤ factorization (default-Z3 parity; Danielle, 2026-07-26 review)

Complete in 4 slices (commits e7b4e41..9a0c69a), full build 7580 jobs
green, 120+ pins. What landed:

1. **`Kernel/Zp.lean` + `Kernel/ZPoly.lean`** — modular context and
   ℤ[x] layer. Fidelity catches: (a) z3's zp is **balanced**
   `(−m/2, m/2]` (`mpzzp_manager::p_normalize_core`), not `[0, m)` —
   load-bearing for `exact_div` and the CRA first image; (b) z3's ℤ gcd
   is `mod_gcd` (231-big-prime table from `polynomial_primes.h`,
   `CRA_combine_images` with balanced reps, primitive-candidate trial
   division, Euclid fallback), not subresultant. **Mathlib reverted
   out of the kernel** after its `!![` matrix-literal token glued
   `![` and broke `x[i]![j]!` chains downstream (AnumEval parse
   error) — local `bezoutCoeffs`/`isqrt` instead; kernel stays
   mathlib-free (per-file elab ~2-4s vs ~15-20s as a bonus).
2. **`Kernel/Factor.lean` GF(p) half** — `zpSquareFreeFactor` (Yun in
   char p with the Frobenius p-th-root step), `berlekamp_matrix` port
   (Q−I recurrence, column-op diagonalize, null-space enumeration),
   `zpFactorSquareFreeBerlekamp` (randomized=false — the deterministic
   path `zp_factor_square_free` actually selects), `zpFactor`.
3. **`Kernel/Factor.lean` ℤ half** — `henselLiftStep`/
   `henselLiftQuadratic`/multi-factor `henselLift` (last factor carries
   `lc⁻¹`), `mignotteBound`, `DegreeSet` (Nat bitset), `CombIter`
   (the `ufactorization_combination_iterator` state machine, faithful:
   removal, size growth, degree-set filter, left/right/tail products),
   `factorSquareFree` (prime trials 2..31, GF(p)-irreducible ⇒ done,
   degree-set-trivial ⇒ done, best-of-trials, Hensel, tail-coeff
   pre-checks, `exact_div` trials, budget ⇒ `false`), `factor2SqfPp`
   discriminant shortcut, `factorCore` (Yun over ℤ via `mod_gcd`),
   `factor`. Pins incl. x⁴−10x²+1 surviving the lifted search and
   x⁶−1 → 4 cyclotomic factors.
4. **RAlg wiring** — `RAlg.root` gains `minimal` (z3 `m_minimal`,
   defaulted ctor arg so bare constructions mean `false`);
   `isolateRoots` = `am::isolate_roots` (zero-strip → factor → linear
   basic → per-factor isolation with `minimal = full_fact` →
   `sort_roots`); `compareCore` **minimal-polynomial
   refine-until-disjoint branch** between `compare_p` and magnitude
   equalization (the COMMON path in default z3); `isRational`
   short-circuits on minimal cells (`m_not_rational` semantics);
   became-basic paths are safety nets, matching default-z3
   radical-only + the F1 guard. `factor=false` leaves the
   approved-divergence register.

Original item text (all consequences landed): port
`upolynomial_factorization.cpp` (~1300 lines): square-free
factorization, Berlekamp over `Z_p` (prime trials per
`factor_max_prime`/`factor_num_primes`), lifting + recombination
(`factor_search_size`). Wire into `RAlg.isolateRoots` per
`am::isolate_roots` (:605): strip zero roots → factor → degree-1
factors become basic `−b/a` directly, higher factors isolate per-factor
with `m_minimal` tracking. Consequences implemented WITH it: cells
gained the `minimal` flag; `compareCore`'s minimal-branch
(refine-until-disjoint) is now the COMMON path and is implemented;
became-basic paths are radical-only (F1 `separate` guard is a pure
safety net); eager rational-root discovery matches default Z3.

**Sequencing decided 2026-07-26 (Danielle's guiding rule, DESIGN-endgame
§6 Q4): EARLY — right after nla-28's signatures, before 12b-ii/12c.**
Build the evaluator/solver once against default parity; re-derive the
affected nla-26 behavioral pins from source during this arc.

## nla-28 `done` (2026-07-28) — anum statefulness threading (Danielle, 2026-07-26 review; sequence BEFORE/WITH 12c)

Landed per the confirmed design (DESIGN-endgame §6 Q2): explicit
refined-arg tuple returns at RAlg + refined-set returns at IntervalSet;
the 12c solver store will own the assignment-level threading.

**RAlg level** (`Kernel/RAlg.lean`): `compare`/`compareCore` →
`Ordering × RAlg × RAlg` (all became-basic re-dispatch paths return the
mutated cells, z3 `return compare(a, b)` shape; root-vs-rat dispatch
stays mutation-free per source); `intLt`/`intGt` → `Int × RAlg` (z3
const_cast, algebraic_numbers.cpp:2830/2843); `select` →
`Rat × RAlg × RAlg` (`separate` already returned the pair); `lt`/`le`
thread through `compare`. **NEW `isRational`** — the
`imp::is_rational` port (`algebraic_numbers.cpp:285`): rational-root-
theorem discovery, refine to width `< 1/2^(log2|aₙ|+1)`, candidate
`⌊u·|aₙ|⌋/|aₙ|` becomes basic on a root hit; `restore_if_too_small`
ported (miss with magnitude below `minMagnitude` restores the input
interval; became-basic always sticks); `m_not_rational` cache flag
declared-not-ported (pure recomputation, same answers; factorization is
its only other setter — nla-27). ℚ-coefficient `aₙ` via positive
denominator-clearing (the CertGen scaling pattern; declared QPoly
divergence unchanged). `sign`/`signOfPolyAt`/`magnitude`/
`compareRootRat` verified mutation-free in source, kept pure.

**IntervalSet level** (`Nlsat/IntervalSet.lean`): `cmpLowerLower`/
`cmpUpperUpper`/`cmpUpperLower`/`adjacent` return refined intervals;
`mkUnion` → `(s1', s2', union)` with write-back threading through the
sweep, compression, and the full-check; `pickInComplement` →
`(witness, s')` threading intGt/intLt/lt/select refinement into the
stored endpoints — and the shared-endpoint scan now calls `isRational`
exactly as z3 does, so root-represented rational endpoints are
DISCOVERED and returned basic: **the root-represented-rational
divergence at this spot is dissolved** (it leaves the approved-divergence
register; remaining there: eager-canonical MPoly, Sturm-vs-Descartes,
QPoly ℚ[x] bridge).

**Acceptance pins (all green):** intGt refinement persists in the
returned set (width < 1/2); root-of-x²−4-in-(1,3) shared endpoint picks
`.rat 2` AND the returned set's endpoint became basic; mkUnion's
√3-vs-√2 sweep compare refines both stored endpoints (exact
(3/2, 2)/(1, 3/2) forms pinned); isRational candidate path finds 1/3
(non-dyadic, never a midpoint); restore_if_too_small pinned at
|aₙ| = 65536 (returns the input cell, not the 2⁻¹⁷-refined one).
Full build 7575 jobs green, all pre-existing suites re-green under the
new signatures.

Z3's anum ops MUTATE cells and the refinement persists in solver state
— `compare`/`select`/`separate` take `numeral&`, and `int_gt`/`int_lt`
even `const_cast` (`algebraic_numbers.cpp:2830`) to refine interval-set
endpoints stored behind const pointers. Our pure ports discard that
work, so later magnitude gates and select niceness see WIDER intervals
than Z3 would — a behavioral divergence (witness drift), not just
performance. Design: RAlg ops return their (possibly refined)
arguments; `IntervalSet` endpoint comparisons and `pickInComplement`
thread updated intervals back into the stored set; 12c's assignment map
stores refined cells after every evaluator/compare call. [medium
refactor, touches IntervalSet comparison helpers + mkUnion + 12b-ii/12c
signatures] **Design CONFIRMED 2026-07-26 (DESIGN-endgame §6 Q2):
explicit refined-arg tuple returns at RAlg + solver-state store at 12c.
This is the next item; complete mutation-site list in DESIGN-endgame
§2.1.**

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

## nla-29 `todo` — anum arithmetic (eval/mul/inv/div) for the q≡0 fallbacks (Danielle, 2026-07-28)

The `q ≡ 0` degenerate fallbacks inside `isolateRootsAt`
(`algebraic_numbers.cpp:2622-2678`: linear-coefficient solve with anum
division, and the auxiliary-z nested path with anum coefficient
evaluation) need anum VALUES — z3's op-by-op algebraic-number
arithmetic: `imp::eval` over `add`/`mul` (both `mk_binary` —
resultant-composed defining polynomial + interval disambiguation),
`neg` (`p_minus_x` + interval negation), `inv` (`p_1_div_x` + rational
interval inversion + `convert_q2bq_interval`), `div` = inv+mul. Port
faithfully (Danielle's call over a resultant-chain shortcut: full
mechanism, no case harder for us than for z3). Then land the two
fallbacks with z3's exact shape, and `isolateRootsAt`'s `none` case
disappears. Sequence: before 12c's conflict path (the solver's
`eval_root`/`infeasible_intervals` hit degenerate traces there).
[medium-large: own arc]

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
  Z3's rational-preference parity). **nla-12a DONE (same day):**
  `Nlsat/Types.lean` (Literal/IneqAtom w/ parity-tagged factors/RootAtom
  per nlsat_types.h; sparse ℚ MPoly with univariate view + QPoly
  bridge) + `Nlsat/IntervalSet.lean` (the mk_union nine-case sweep
  transcribed 1:1 incl. justification-preserving splits,
  same-justification-only compression, slack/full computation;
  pickInComplement deterministic preference ladder: zero → int above →
  int below → gap rational → shared rational endpoint → irrational
  witness; declared divergences: am.select dyadic niceness, rational
  values in root representation). Tests pin union cases + the full
  preference ladder. Trace.lean deferred to 12d (payloads pin when the
  checker consumes them, per design). **anum decision (Danielle,
  2026-07-26): Z3's actual shape, similarity uncompromised** — full spec
  in DESIGN-nlsat-quadratic §4b. **nla-12b-i DONE (same day):**
  `Nlsat/AnumEval.lean` — exact-Rat interval arithmetic w/ even-power
  tightening + MPoly enclosure evaluation; `resultantElim` (the ONE
  resultant shape both call sites need: second argument is always a
  univariate rational defining poly — multiplication-matrix det mod
  monic q̂, faithful lc/sign scalars); `nonzeroRootLowerBound`
  (reverse-Cauchy 2^−k); RAlg interval accessors + width-gated
  refinement. Tests pin the classic eliminations (√2 minimal poly, √6,
  √2+√3 → x⁴−10x²+1, non-monic scaling). **nla-12b-ii DONE
  (2026-07-28):** `Nlsat/Evaluator.lean` — `evalSignAt` (:2246:
  optimistic → rational-fragment substitution → magnitude-gated
  interval refinement → exact resultant zero test with `L = 2^{−k}`,
  nla-28 threaded incl. `save_intervals` restore semantics);
  `isolateRootsAt` (:2547: shortcuts → substitute → stable degree-sorted
  resultant elimination → kernel isolation → `filter_roots`;
  `var_degree_lt`'s UINT_MAX-for-unassigned caught and ported — the
  target sorts last); `isolateRootsSigns` (:2902: refine to
  DEFAULT_PRECISION=2, `intLt`/`select`/`intGt` samples as rational
  defaults). `Nlsat/EvaluatorTable.lean` — `SignTable` (merge with
  nla-28 compare threading, add/addConst/signAt linear branch — binary
  branch is value-identical, declared non-divergence), `satisfied`*,
  `evalIneq`/`evalRoot` (undef-share threading caught: the target's
  value is re-attached after isolation), `infeasibleIntervalsIneq`
  (cell sweep; **review catch: `neg` must feed `satisfied` in the
  sweep**, first pass dropped it) + `infeasibleIntervalsRoot` (the
  ROOT_EQ/LT/GT/LE/GE case table). **q ≡ 0 fallbacks → nla-29**
  (Danielle 2026-07-28: full anum-arithmetic arc first — they need
  anum VALUES). 26 pins green incl. resultant zero test, ±2^{1/4}
  through eliminate→isolate→filter, q≡0 → none, sign-table sweeps
  both variants, eval predicates.
  **CELL-STORE REFACTOR (2026-07-28, post-12b-ii design review,
  Danielle-approved):** z3's two statefulness mechanisms mapped to two
  layers — op level stays the nla-28 tuple ops in RAlg (untouched),
  owner level (x2v, interval endpoints, undef/ext sharing, trail)
  becomes `Kernel/CellStore.lean`: `CellStore = Array RAlg` +
  `CellM = StateM CellStore`, in-place updates so became-basic and
  refinement are visible to every holder (versioned ids would have
  reintroduced the threading bug). `IntervalSet` endpoints and
  `Assignment` bindings are `CellId`s; the nla-28 write-back machinery
  collapsed into store semantics (mkUnion returns just the union again;
  `evalRoot`'s re-attachment hack deleted — that bug class is
  structurally impossible). All pins re-derived and green. TWO STORE-ERA
  LESSONS: (a) `CellId`s dangle outside the store that allocated them —
  test helpers that build sets in separate `run'` calls then mix them
  read out-of-bounds (panic-returns-default, F7 again); every mixed-set
  scenario runs in ONE `CellM` computation. (b) `fresh` written as
  `let s ← get; set (s.push c); return s.size` keeps `s` borrowed
  across the push → RC>1 → full array copy per allocation → quadratic
  blowup in allocation-heavy loops (the mkUnion differential went 7s →
  >300s); write it `let n := (← get).size; modify (·.push c); return n`
  and avoid per-probe allocations (root-vs-rat compares are
  mutation-free → pure reads).
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
