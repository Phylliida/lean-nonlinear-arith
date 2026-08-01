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

## nla-29 `done` — anum arithmetic (eval/mul/inv/div) for the q≡0 fallbacks (Danielle, 2026-07-28; closed 2026-07-31)

**Design review (2026-07-31, post-close):** one F3-class fix landed
(mkBinary became-basic restore ordering — z3's destructor semantics mean
`mk_basic` sees the OVER-REFINED b on the a-path, and the b-path returns
the post-`mk_basic` a WITHOUT a final restore; first cut restored both
before re-dispatch. Judged nearly-unreachable in practice — getting a
cell below minMagnitude inside a mk_binary loop needs ~17 failed scans —
so no distinguishing pin; argued from source; suite re-green). Verified
clean against source: sign-variation zero-skip conventions identical
(:1895); deg-1 collapse is exact parity with z3's `set` (:481-487), not
a divergence; target-factor V ≥ 1 always (non-root-endpoint invariant
makes r_i's bracket strict) so the discard loop can never drop the
target — no infinite-loop corner; aux-z z-shadowing ≡ z3's ext_var2num
within the nested call; convert(x, i−1) truncation exact (:7718).

**Review follow-ups (Danielle's directives, 2026-07-31 — "nearly
unreachable still needs fixing"; "identical behavior in practice";
"cover all cases"; "prove the termination arguments"):** ALL LANDED.
(1) `evalCore`/`evalAnum` return `Option` — an unassigned variable is a
`none`, never the panic-default silent cell-0 read. (2) z3's throw
paths are `Option` too: `inv`/`div` of zero, `power` 0^0 — `none`
propagates (the faithful image of the exception unwinding out of the
nlsat call), replacing Lean's silent `1/0 = 0` / `0^0 = 1`; pins cover
the `none` cases. (3) `detBiv` is now Bareiss fraction-free (O(n³) poly
muls, exact over ℚ[x] at ANY matrix size) — first cut had a real bug
(skip-on-zero-entry dropped the pivot scaling; caught by the
composeXDivY pins); Laplace kept as the differential reference, pinned
equal on a specimen family. (4) Termination: the ops are now
non-recursive — became-basic is DATA (`MkBinaryResult`/`MkUnaryResult`
carrying the discovered rational; the caller re-dispatches through
`*RatL`/`*RatR` = `mk_basic` with a basic operand) instead of a
callback into the full op; `isolateRootsAt` split into
`isolateRootsAtCore` + `isolateRootsNested`/`isolateRootsAt`
(structural, no `partial`, the one-level nesting is now by
construction); `evalCore` has a real `termination_by x` (the variable
decreases; `maxSmallerThan` returns a proof-carrying subtype).
Remaining `partial` (analytic termination): **nla-31** below.
(5) CellStore lifts consolidated into `CellStore.lean` (which now
imports AnumArith); the `MkBinaryOps`/`MkUnaryOps` records are gone
(plain parameters). (6) eval-walker temp analysis agreed — recheck if
12c ever reuses temporaries across op calls.

## nla-31 `todo` — termination proofs for the analytic walks/loops (Danielle, 2026-07-31)

The remaining `partial` defs in the anum layer, with the shape of each
argument. Danielle's directive: build and PROVE the termination
arguments properly.

- **`mkBinary`/`mkUnary` loops**: each iteration strictly halves both
  isolating intervals (or exits became-basic). The target factor's
  `V ≥ 1` at every iteration (its root is strictly inside `r_i` by the
  non-root-endpoint invariant); distinct factors have distinct roots
  (factorization correctness), so once the interval is narrower than
  every root-gap the scan yields a unique `V == 1`. Needs: correctness
  of `Factor.factor` (product of distinct square-free factors ∼ p, no
  shared roots), Sturm count correctness (**nla-10**), root separation
  (square-free ⇒ nonzero minimum gap).
- **`isolating2Refinable` walks** (cases 2–4): the halving walk reaches
  a point whose sign differs from the endpoint sign (or the exact
  root). Existence of that point follows from the `V == 1` count +
  square-freeness (the root is simple, so the sign changes across it) —
  same nla-10 flavor.
- **`refineNzBound` walks**: sign stability of a polynomial near a
  NON-root point — elementary (continuity-style: `p(0) ≠ 0` ⇒ sign
  eventually constant on the halving sequence); does NOT need Sturm.
  Cheapest of the bunch, do first.
- **Pre-existing partials in the same class** (include in scope):
  `Mpbq.refineUpper`/`refineLower` (dyadic grid finer than
  `|q − dyadic|` with `q` non-dyadic), `refineToPrecD` (width gate
  halves), `compareCore`'s loops, `separate`, `selectSmallCore*`,
  `BivPoly.detBivLaplace` (structural on matrix size — actually easy:
  recursion on `n`).

Sequencing: the elementary ones (refineNzBound, refineUpper/Lower,
detBivLaplace) are independent; the Sturm-flavored ones (mkBinary,
mkUnary, isolating2Refinable) compose with nla-10.

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

Slice plan (2026-07-31, source-anchored to algebraic_numbers.cpp unless
noted; 29.1 decision resolved below):

- **29.1 kernel gadgets** `done` (2026-07-31): `QPoly.pMinusX` /
  `p1DivX` / `composeAnPXDivA` / `translateQ` / `composePQX` in
  `Kernel/QPoly.lean` (verbatim ports, z3's positive scalar factors
  preserved); `convertQ2BqInterval` in `Kernel/Roots.lean` (returns
  `Mpbq ⊕ (Mpbq × Mpbq)` — `.inl` = exact-root discovery during the
  walk, which z3 reports as `false`+root-in-`c`; 29.3 call sites treat
  it as became-rational); `Kernel/BivPoly.lean` ((ℚ[x])[y] dense,
  `composeXMinusY`/`composeXPlusY` Horner, `composeXDivY` direct,
  `modMonic`/`powModTableB`, `detBiv` Laplace — exact over the ring
  ℚ[x], exponential in d = deg pb, nla-30 if deep nesting demands
  Bareiss; `resultantElimY` = lc(pb)^degF·det, NO parity factor per the
  25.3 lesson). Pins: hand-traced z3 walks (4/3 → c=11/8 d=3/2;
  7/5..10/7 → 721/512, 91/64; walk root-hit .inl 3/8) + √2+√3 ↦
  x⁴−10x²+1 (differential vs the AnumEval pin), √2·√3 ↦ (x²−6)²,
  non-monic 4x⁴−28x²+1, linear, (x²−4)². Original slice text kept:

  Original scope: `pMinusX` (p(−x), odd-coeff sign flip — `p_minus_x`, used by neg
  :1784); `p1DivX` (x^n·p(1/x) = coefficient reversal — `p_1_div_x`,
  used by inv :1847); `translateQ` (p(x−q) Taylor shift — `translate_q`
  :1608, algebraic+basic add); `composePQX` (q^n·p(x/q) —
  `compose_p_q_x` :1716, algebraic×basic mul); `convertQ2BqInterval`
  (rational interval → tight dyadic bracket — upolynomial.cpp:2833;
  inv and both mixed basic/algebraic paths funnel through it).
  Bivariate resultant shapes for mk_binary: represent (ℚ[x])[y] as
  `Array QPoly` (poly in y with QPoly coeffs); `composeXMinusY` /
  `composeXPlusY` (mk_add_polynomial :1000-1019) and `composeXDivY`
  (y^n·pa(x/y), mk_mul_polynomial :1028-1044), then eliminate y against
  the univariate pb(y). **Decision (Danielle, 2026-07-31): extension
  APPROVED** — the capability sets are identical on every reachable
  input (both routes compute the exact mathematical resultant; the
  determinant identity `Res(f,g) = lc(g)^{deg f}·det(mult-by-f mod ĝ)`
  is a theorem, not an approximation, valid for all f and all pb with
  deg ≥ 1). The only inputs z3's general multivariate resultant handles
  beyond this are multivariate second arguments, which no reachable
  call site produces (the second argument is always a univariate
  defining poly). Deferred-generality work recorded as **nla-30**.
- **29.2 mk_binary/mk_unary engine** `done` (2026-07-31, engine half):
  `Kernel/AnumArith.lean` — `mkBinary` (:1210) verbatim: resultant-composed
  poly (BivPoly route) → nla-27 factor → per-factor `sturmChain` (|lc|-
  normalized; positive rescaling preserves the V counts) → discard/target
  scan with the UINT_MAX analogue → `setCore` (:1150: zero-snap via
  `signVarAt seq 0`, zero-strip, new `isolating2Refinable` in Roots.lean —
  all 4 cases) → refine with z3's short-circuit `!refine(a) || !refine(b)`
  became-basic re-dispatch. `save_intervals` semantics:
  `restoreIfTooSmall` on BOTH exits (z3's duplicate `saved_a` call at
  :1285-1286 is a no-op; saved_b is restored by its destructor — net
  effect both, ported as both). mk_unary NOT ported: only serves k-th
  roots/powers (:1550/:1580), unreachable from our op set. MpbqI moved
  Nlsat/AnumEval → Kernel/Mpbq (mk_interval functors need it; resolves
  via the existing `open`). Original slice text kept:

  Original scope: factor
  (nla-27) → sturmChain per factor → signVarAt at r_i endpoints →
  discard/target loop (V≤0 discard, V==1 target, else keep) →
  refine a/b with became-basic re-dispatch to mk_basic
  (add_proc/sub_proc/mul_proc :1077-1099) → save_intervals /
  restore_if_too_small (nla-28 semantics) → set_core (:1150: interval
  contains 0 ∧ p has zero root ⇒ reset to rational 0; else mkRoot with
  minimal flag + am::normalize zero-straddle). CellM threading
  throughout (refine mutates cells); store-era lessons apply: one
  CellM computation per scenario, `modify`-style fresh, no per-probe
  allocations on mutation-free paths.
- **29.3 the ops** `done` (2026-07-31, with 29.2): dispatch tables
  verbatim in `Kernel/AnumArith.lean` — add/sub (zero shortcuts,
  basic+basic, algebraic+basic via `addAlgebraicBasic` = translateQ with
  to_mpbq fast path + convertQ2BqInterval fallback, algebraic+algebraic
  via mkBinary IsAdd); mul (zero reset, `mulAlgebraicBasic` = composePQX
  with negative-scalar endpoint swap, mkBinary); neg (pMinusX + interval
  negation); inv (`refineNzBound` FIRST — div2 walk with root-hit ⇒
  became basic; then p1DivX + rational endpoint inversion + swap +
  convertQ2BqInterval); div = inv + mul on a COPY of the divisor (b never
  mutated). Two declared z3-bug-side treatments (verdict-preserving, in
  the file header): (1) add/mul mixed-path convert exact-root ⇒ z3 logs
  "conversion failed" and calls set with a STALE upper bound (:1629/:1742)
  — we return `.rat` of the found root (the value IS that dyadic);
  (2) inv's convert exact-root ⇒ z3 THROWS (:1858), aborting the nlsat
  call — we return `.rat` (can only continue where z3 fails, never the
  reverse). Division-by-zero is UNREACHABLE in z3 (throws); our callers
  pre-discharge ≠0 (29.5's linear solve checks `!is_zero(a1)` first) —
  explicit precondition, no panic-guard reliance (F7 lesson).
  Pins (AnumArithTests): √2+√3 .eq to the isolated x⁴−10x²+1 cell,
  √2·√3 = √6 .eq, √3−√2 small root, neg/inv/div, non-dyadic mixed paths
  (√2+1/3, √2/3), and the DESIGNED became-basic pin: x²−4 cell (1,3) +
  −√3 cell (−32,−1) — sum interval covers both result factors so the
  first scan leaves 2 candidates, first refine bisects at exactly 2 ⇒
  a' == .rat 2 persisted, result 2−√3. CellStore lifts addC/subC/mulC/
  negC/invC/divC pinned through the store. Original slice text kept:

  Original scope: (:1584-1883), dispatch tables verbatim: add/sub
  (zero shortcuts, basic+basic, algebraic+basic via translateQ with
  to_mpbq fast path + convertQ2BqInterval fallback, algebraic+algebraic
  via mk_binary IsAdd); mul (zero reset, basic scaling via composePQX
  with negative-scalar endpoint swap, mk_binary); neg (pMinusX +
  interval negation + update_sign_lower); inv (refine_nz_bound FIRST
  :1794-1833 — div2 walk until endpoint sign matches cell sign, root
  hit ⇒ becomes basic; then p1DivX + rational endpoint inversion + swap
  + convertQ2BqInterval); div = inv + mul (:1868). Division-by-zero is
  UNREACHABLE in z3 (throws); our callers pre-discharge ≠0 (the 29.5
  linear solve checks `!is_zero(a1)` first) — mirror as an explicit
  precondition, no panic-guard reliance (F7 lesson).
- **29.4 imp::eval walker** `done` (2026-07-31): `evalAnum`/`evalCore`
  in `Nlsat/Evaluator.lean` — `t_eval`/`t_eval_core`
  (polynomial.cpp:6676/6749) verbatim: Horner over the max var with
  recursive coefficient evaluation (`maxSmallerThan` =
  polynomial::max_smaller_than), group splitting on x-degree drops,
  single-monomial ascending-var walk. z3 lex-sorts first; our MPoly is
  already canonical (approved eager-sort). Stored-cell refinements
  persist via the ops' write-backs (z3 reaches them through the public
  const_cast wrappers — probe-confirmed :3268-3300: the "const&" ops
  mutate); temps are overwritten per op in both worlds, so no temp
  threading. Required `RAlg.power` (z3 `power` :1559 via a new
  `mkUnary` engine in AnumArith.lean — this board's earlier "mk_unary
  unreachable from our op set" note was WRONG: t_eval's
  `vm.power(x2v(y), d, …)` reaches it; `xMinusYPow` =
  resultant_y(x−y^k, pa(y)), `MpbqI.pow` interval, power_proc
  re-dispatch).
- **29.5 q≡0 fallbacks in isolateRootsAt** `done` (2026-07-31): linear
  solve (eval c0/c1; a1 == 0 ⇒ no roots; else root = −a0/a1 via
  div+neg); auxiliary-z (first non-vanishing coefficient scan i = n..1;
  all vanish ⇒ no roots; else q2 = z·xⁱ + (p' capped at x-degree i−1),
  z ↦ a, nested call with the flag — `partial`, z3 caps nesting at one
  level by SASSERT). `none` survives only for the z3-SASSERT-violation
  case (nested ∧ q ≡ 0). WITNESS ANALYSIS (corrects the acceptance
  sketch below): q ≡ 0 needs ONE factor F of the (square-free, possibly
  reducible) defining poly d dividing EVERY x-coefficient of p'; if F's
  root IS the assigned value, all coefficients vanish (the no-roots
  case); if it is a DIFFERENT factor's root, none vanish and aux-z
  fires with i = n. The "(y²−2)·x² + x + c ⇒ aux-z z↦1" sketch was
  wrong — the resultant does not vanish there (normal path handles it).

Acceptance pins landed (EvaluatorTests + AnumArithTests): √2+√3 ↦
x⁴−10x²+1 cell (differential vs the AnumEval pin), √2·√3 = √6, −√2,
1/√2, div roundtrip; mixed basic/algebraic √2+1/3 and √2/3 (non-dyadic
⇒ convertQ2BqInterval fallback); the designed became-basic mid-mkBinary
pin (a' == .rat 2 persisted); evalAnum: x²+y² ↦ 5, x·y ↦ √6,
x³−xy ↦ −√2; q≡0 witnesses: x·(y²−2) at √2 ⇒ #[] (the stale `none`
pin updated — z3 returns empty roots there), (y²−3)(x−1) at the
√2-root-of-(y²−2)(y²−3) cell ⇒ root 1 via div+neg, (y²−3)(x²−x−1)
same cell ⇒ aux-z ⇒ exactly {(1±√5)/2} (.eq to isolateRoots of
x²−x−1; the filter drops 0 and ±√(1+√2)), (y²−2)(x²+x+1) at √2 ⇒ #[].

Original acceptance sketch (for the record): √2+√3 lands on an x⁴−10x²+1 cell (differential vs the
AnumEval pin), √2·√3 on the √6 cell, −√2 sign+interval flip, 1/√2,
(a/b)·b ≡ a under compare; mixed basic/algebraic √2 + 1/3 (non-dyadic
basic ⇒ convertQ2BqInterval fallback path); became-basic mid-mk_binary
re-dispatch (one argument discovers rationality during refinement);
q≡0 witnesses: (y²−2)(x+1) at y↦√2 ⇒ no roots (all coefficients
vanish), (y²−2)·x² + x + c at y↦√2 ⇒ auxiliary-z path fires with z↦1
[wrong — see the witness analysis above].

## nla-30 `todo` — general multivariate resultant (deferred; Danielle 2026-07-31)

The multiplication-matrix elimination route (resultantElim in 12b-i,
extended to mk_binary's shapes in nla-29) covers every reachable call
site: the second argument is always a univariate defining poly. z3's
general multivariate resultant (`polynomial.cpp` manager::resultant)
also accepts multivariate second arguments; no reachable call site
produces those today, but Tier B (full-degree projection, nla-11/nla-13)
and any future elimination shape may. When the first such call site
lands, port the general mechanism (or a value-exact equivalent with a
provably identical capability set — the bar Danielle set for the 29.1
decision). Until then the extended route stands on the
capability-identity argument: both routes are exact on every reachable
input.

## nla-32 `done` (2026-07-31) — 4.12.5 re-anchoring audit (found in the 12c planning sweep, 2026-07-31)

**OUTCOME (audit complete, 2 fixes landed, everything else verified
clean):** every cluster classified hunk-by-hunk. TWO semantic
divergences found and re-anchored; the rest of the 4.12.5↔HEAD delta
is mechanical or HEAD-only additions correctly absent from the port.

**Fix 1 — `pickInComplement` (IntervalSet.lean):** re-anchored to
4.12.5's `peek_in_complement` ladder: dropped the post-4.12.5
zero-first scan (`cmpWithZero` deleted) and swapped the int branches
back to 4.12.5 order (int_below FIRST, then int_above). 3 new
differential pins on shapes where the texts select different
witnesses ((2,3) → 1, (−5,−3) → −6, (−∞,−2) → −1); all prior pins
re-green unchanged (they were designed zero-excluded or on unchanged
branches).

**Fix 2 — `intLt`/`intGt` (RAlg.lean):** HEAD added
`refine_until_prec(a, 1)` + `const_cast` mutation to `int_lt`/`int_gt`;
4.12.5 reads `⌊lower⌋`/`⌈upper⌉` off the CURRENT dyadic bounds and
never mutates. Re-anchored: `RAlg.intLt/intGt : RAlg → Int` (pure,
tuple return gone), CellStore lifts are pure reads. Pins re-derived:
the intGt-witness value is unchanged on the fixtures (⌈2⌉ = 2) but
the stored endpoint is now asserted UNCHANGED (was: refined to width
< 1/2 — HEAD behavior). `isolateRootsSigns` unaffected (its
`refine_until_prec(roots, DEFAULT_PRECISION)` IS in 4.12.5; the
samples read the refined bounds exactly as z3 does there).

**Verified clean (mechanical or HEAD-only):** nlsat_interval_set
beyond pick (mk_union sweep, get_justifications, get_interval);
nlsat_evaluator.cpp (100% mechanical); nlsat_types/assignment/
justification/clause headers (levelwise-era additions: clause
bitfields, indexed_root, internal_assumption — all absent at 4.12.5);
algebraic_numbers.cpp rest (isolate_roots_closest, isolate_kth_root,
sign_variations_at_mpq, display_root_common = HEAD additions for
levelwise; `checkpoint()` insertions + compare_core's
cancel-path `return sign_zero` → `throw` = cancellation semantics,
no port impact — budgets land at nla-14); polynomial.cpp (t_eval_core,
substitute, uni_mod_gcd, lex_compare, graded_lex_compare, both
`rename`s, `resultant` — function-level diffs IDENTICAL modulo
mechanical; `peek_fresh`'s added `p_normalize` is multivariate-gcd
only, unreachable from our univariate modGcd; large_mul_buffer is
`#if 0` dead); polynomial_cache (additive `contains_chain`);
upolynomial.cpp + upolynomial_factorization.cpp (100% mechanical —
nla-27 stands); mpbq (mechanical); nra_solver.cpp (entry confirmed
at 4.12.5: `alloc(nlsat::solver, …, false)` incremental=false,
single-factor `is_even=false` literals, no-assumption `check()`;
order is restored INSIDE nlsat check() at 4.12.5 — matches 12c.6).

**Doc debt (recorded, low value):** docstring line anchors throughout
the ported files reference the working-tree (4.16-nightly) numbering;
semantics now target 4.12.5 (the two re-anchored sites cite 4.12.5).
A renumbering pass is optional. **12d note stands:** re-anchor
DESIGN-nlsat-quadratic's nlsat_explain.cpp line anchors to 4.12.5
when 12d opens (levelwise absent there = classic path is the whole
file).

Original entry (the audit spec, kept for the record):

**Finding:** the workspace z3 checkout is 4.16-nightly
(`z3-4.16.0-1024-gffe29b143`), but the parity target is **4.12.5**
(verus-dev's shipped z3 — DESIGN-endgame §2.3 pins it). Prior arcs
read the working-tree text. Diff volume 4.12.5↔HEAD on the ported
sources: `nlsat_solver.cpp` 2464 lines, `nlsat_explain.cpp` 1338,
`polynomial.cpp` 1145, `algebraic_numbers.cpp` 528,
`nra_solver.cpp` 387, `upolynomial.cpp` 347, `nlsat_interval_set.cpp`
170, `upolynomial_factorization.cpp` 120, `nlsat_evaluator.cpp` 97,
`nlsat_types.h` 50. Most hunks are mechanical (prefix-increment #8199,
copy-elision #8589, structured-bindings #8425, lws merge, TRACE
renames) — but not all.

**Confirmed semantic divergence (seed finding):** our
`IntervalSet.pickInComplement` follows HEAD's `pick_in_complement`;
4.12.5's `peek_in_complement` differs twice at `randomize=false`:
(1) HEAD first scans all intervals for 0-coverage and picks **0**
whenever no interval covers it; 4.12.5 picks 0 ONLY for the null set.
(2) HEAD tries `int_gt(last.upper)` BEFORE `int_lt(first.lower)`;
4.12.5 is the reverse. Both change the selected witness on identical
states (e.g. set `{(−∞,−2)}`: HEAD → 0, 4.12.5 → −1; set `{(1,3)}`:
HEAD → 0, 4.12.5 → 0 — same by luck; single bounded interval with
positive lower: HEAD → above, 4.12.5 → below). Witness-level only —
any complement member is a valid witness — but rule 3 applies.
**DECIDED (Danielle, 2026-07-31): re-anchor** to the 4.12.5 ladder
(drop the zero-scan, swap the int order) and re-derive the affected
12a/28 pins.

**Scope** (per cluster: classify each 4.12.5↔HEAD hunk mechanical vs
semantic; check which text the port follows; re-anchor to 4.12.5 or
register a divergence with sign-off):
- `nlsat_interval_set.{h,cpp}` — pick (above), the mk_union sweep,
  get_justifications, get_interval.
- `nlsat_evaluator.cpp` — infeasible_intervals / eval / sign table.
- `nlsat_types.h` / `nlsat_assignment.h` / `nlsat_justification.h` —
  likely mechanical.
- `algebraic_numbers.cpp` — the anum layer (the nla-26/28/29 surface:
  compare_core ladder, refine_core, is_rational, select, int_gt/lt,
  mk_binary/mk_unary, imp::eval, isolate_roots, eval_sign_at).
- `polynomial.cpp` — t_eval walker, substitute, max_smaller_than,
  `rename` (12c's reorder consumes it), monomial orders.
- `upolynomial.cpp` + `upolynomial_factorization.cpp` — isolation
  anchors, nla-27 factor.
- `mpbq.h/cpp` (small), `basic_interval.h` (unchanged),
  `nlsat_params.pyg` (unchanged), `nlsat_justification.h` (unchanged).
- `nra_solver.cpp` — the consumer entry (incremental=false, no
  assumptions, mk_literal shapes, restore_order after) — re-read at
  4.12.5 to confirm.
- `nlsat_explain.cpp` — 12d's spec; DESIGN-nlsat-quadratic's line
  anchors came from HEAD, re-anchor them when 12d opens (levelwise is
  absent at 4.12.5, so the classic path IS the whole file — that part
  of the design stands).

Method = the standing review method (re-read z3 against the port),
now against `git show z3-4.12.5:<path>` as the text. **Source-of-truth
rule going forward: all nlsat ports cite the 4.12.5 text, never the
working tree.** Estimate 1–2 sessions. Sequenced BEFORE 12c —
select_witness sits on pick, and 12c's acceptance pins must be
derived against the final anchor.

## nla-12c design review `done` (2026-07-31, Danielle-requested, post-close)

Method: the standing one — adversarial re-read of
`git show z3-4.12.5:src/nlsat/nlsat_solver.cpp` (+ `mk_root_atom`,
`flip_sign_if_lm_neg`, interval_set) against the port, hunting
divergences, uncovered cases, and regrettable decisions.

**TWO FIXES LANDED:**
1. `renameAtoms` renamed root-atom polys but not the atom's `x` —
   z3's `pm.rename` renames ALL variables. Unreachable today
   (`can_reorder` is false when root atoms exist), but "nearly
   unreachable still needs fixing" — fixed + pin (calls renameAtoms
   directly since the guard blocks the reorder path).
2. `mkRootAtom` missed z3's normalization: `flip_sign_if_lm_neg`
   (negate the poly when the graded-lex-max monomial's coefficient is
   negative — roots unchanged, but it is z3's stored form and dedup
   key). Fixed: `MPoly.flipSignIfLmNeg` (uses 25.4's gradedLexCompare)
   applied at creation + pins (normalization, dedup across the sign
   flip). Also noted: z3's `root_atom` sets max_var to exactly `x`
   (SASSERT `x ≥ max_var(p)`); ours computes `max(x, p.maxVar)` —
   more defensive, identical under the invariant.

**VERIFIED CLEAN (line-diff / source re-read):** the subset sweep
(four cases, loop-exit semantics); the pick ladder incl. z3's
JUSTIFIED `irrational_i != UINT_MAX` SASSERT (infinite outer bounds +
no strict gaps + not-full ⇒ a both-open pair exists — proof recorded);
resolve (per-round top reset, decision literal = negated current
value, remove-from-lvl + undo interaction, lemma_is_clause shortcut,
goto start); propagate-then-conflict; watch snapshot vs z3's live
iteration (learned clauses are processed explicitly by resolve —
unobservable); `justifications` clause-id dedup vs z3's no-dedup
(consumed only by the dead assumption layer); undo quirks; m_zero
(display getter); patch/undo_to_base (not called by nra@4.12.5);
reinit_cache/m_cache (explain's cache — lands with 12d);
reset/clear (solver-reuse API — nra allocates per check; 14 creates
fresh Solver per goal, equivalent).

**DECISIONS REVIEWED AND KEPT:** single clause table + learned flag
(all z3 two-table iteration sites mapped: collector=all, full-dim=
input-only, canReorder=all, reattach=all); removeLearnedRoots no-op
(parity argument — **12d must port real deletion + del_clause when
explain's root atoms arrive**); Option for null_var (optVarLt
replicates UINT_MAX incl. poisoning); mockExplain in the production
file (test-only, replaced at the ExplainFn boundary by 12d);
ExplainFn Option-wrapped (29.5 uniformity); watch sorting = z3's
degree_lt position tiebreak exactly; stable clause ids (del_clause
unreachable under the entry).

**12d carry-overs (also in 12c.6/HANDOFF):** explain line anchors
re-anchor to 4.12.5 (levelwise absent there); root atoms are created
via `Solver.mkRootAtom` (dedup + flip normalization live there);
`m_cache` (mk_unique/psc-chain/factor caches) lands with explain.

## nla-12c `done` (2026-07-31, same day as the spec) — the solver loop

**CLOSED — all six slices landed, full build green (7590 jobs), 50+
new pins.** `Nlsat/Solver.lean` (+ `SolverTests.lean`).

- **12c.1 scaffold** `done`: LBool, Justification (null/decision/
  clause/lazy — z3's tagged pointer as an inductive), TrailEntry
  (5 kinds), Solver record + `SolverM := StateM Solver` + `liftC`,
  mk_bool_var/mk_var/mk_true_bvar, atom table WITH hash-consing
  (structural-equality scan — creation is frontend-driven, not hot;
  `DecidableEq` added to the atom types), max_var/max_bvar/degree
  family (incl. null-poisoning of `max_var(sz, cls)` — z3's UINT_MAX
  null is the GREATEST, replicated via `optVarLt`), `lit_lt` (semantic:
  fixes first_undef selection order), mk_clause (sort + attach),
  bwatches/watches attachment.
- **12c.2 trail + undo + assign + value** `done`: the full save/undo
  family VERBATIM incl. `undo_new_stage`'s decrement-then-reset quirk
  (the exited stage KEEPS its assignment — probed and pinned) and the
  `m_bk` rewind; updt_eq with all gates + degree ordering; evaluator-
  backed value/is_satisfied/is_inconsistent with Option threading
  (29.5 ruling). **Lesson (pinned in `Solver.run'`): the derived
  `Inhabited` ignores structure field defaults** — `simplifyCores`
  came out false; use `{}` (`Solver.empty`), never `default`.
- **12c.3 propagation** `done`: `IntervalSet.subset` (z3's two-pointer
  sweep, verbatim cases), R_propagate (lazy justifications carry core
  literals + CLAUSE IDS — the 12b-ii clauseId seam turned out to
  exist already), updt_infeasible, the four infeasible-set cases
  verbatim. **Behavior pin worth remembering:** propagate-then-
  conflict — after R_propagate falsifies the last undef literal,
  num_undef == 0 ⇒ z3 returns false (conflict) — the pins assert
  exactly that.
- **12c.4 search SAT-mode** `done`: peek_next_bool_var (exhausted bk
  STAYS exhausted — null ≠ 0), is_satisfied (null xk = UINT_MAX ≥
  num_vars, matched), select_witness on the re-anchored pick ladder,
  init_search, `search` with resolve-as-parameter. Acceptance pins
  verify models by evaluation (z3's check_satisfied CASSERT made
  external): boolean-only (negative-first decide), one-var algebraic,
  two-var conflict-free, EQ atom with the shared-endpoint irrational
  witness, stub-resolve abort on genuine conflict.
- **12c.5 resolve** `done`: process_antecedent/resolve_clause/
  resolve_lazy_justification (explain as the `ExplainFn` param pinned
  to `nlsat_explain.h`@4.12.5 — projection literals returned, resolve
  appends the negated core), only_previous_stages/max_scope_lvl/
  remove_literals_from_lvl/is_bool_lemma/find_new_level_arith_lemma/
  lemma_is_clause, both backjump cases, learned clauses, the goto-
  start loop. mockExplain for tests is faithful for boolean + stage-0
  conflicts (nothing below to project). Pins: trivial UNSAT, chained
  resolution with learned unit + level-0 empty lemma, stage-0 arith
  UNSAT, case-1 stage backjump + goto start, case-2 decision reversal
  to SAT, max_conflicts gate.
- **12c.6 reorder + check shell** `done`: var_info_collector/
  reorder_lt/heuristic_reorder/reorder/restore_order verbatim
  (reset+reattach ARITH watches only — z3 keeps bwatches; permuted
  assignment built BEFORE undo; `pm.rename` as `MPoly.renameVars`
  over the atom table — cells are var-free, untouched),
  sort_watched_clauses (z3's degree_lt tiebreaks by ORIGINAL
  POSITION — total order, no tie divergence), is_full_dimensional
  (stored for 12d), check()/search_check. **`remove_learned_roots`
  is a no-op with a written parity argument** (observable only under
  incremental reuse, which the one-shot nra entry never does;
  **12d follow-up:** port real deletion + the del_clause machinery
  when explain-produced root atoms arrive). 12e seam marked in
  search_check (real-valued; the integer B&B loop lands at 12e
  before any consumer).

Original spec (the planning-sweep entry, kept for the record):

Port `nlsat_solver.cpp` classic search at **4.12.5**
(`git show z3-4.12.5:src/nlsat/nlsat_solver.cpp`, 3743 lines — NOT the
working tree, which carries #8425/#8498/try_reorder/gc/simplify hooks
that postdate the parity target). Entry shape from
`nra_solver.cpp` (the only consumer on the Verus path):
`nlsat::solver(lim, params, /*incremental=*/false)`, `mk_var(is_int)`,
`mk_ineq_literal` (single-factor, `is_even=false`), unit `mk_clause`s,
`check()` (NO assumptions), `restore_order()` after. Everything the
port builds is reachable from that entry or explicitly listed dead.

**Dead under this entry (declared non-ports, each parity-inert):**
assumption manager (`m_asm`/`m_lemma_assumptions`/`get_core`/
`check(assumptions)` — never called; `m_lemma_assumptions` stays null
in resolve); gc (does not exist at 4.12.5); restart policy (does not
exist — Q3's "restart policy ported verbatim" is vacuous here;
"minimization" = `remove_literals_from_lvl` inside resolve, which is
ported, plus explain's `minimize_cores=false`, 12d scope);
`simplify()`/`inline_vars` (flag false); `shuffle_vars`
(random_order=false); `check_lemmas`/`log_lemmas`/`m_valids` (debug);
`fix_patch` body (`m_patch_var` always empty — keep field + empty
loop); `checkpoint()` (rlimit cancel — no-op with a note; budgets land
at nla-14 per the withLayerHeartbeats directive); levelwise
(post-4.12.5 entirely).

**Reorder is LIVE, DECIDED (Danielle, 2026-07-31): port verbatim.**
`check()` calls `heuristic_reorder()` (reorder default true,
`can_reorder()` true pre-search since learned is empty and no root
atoms yet) and `restore_order()` after; nra_solver reads the model
post-restore. DESIGN-nlsat-quadratic's "no reorder in v0" note
predates this finding. Reorder changes stage structure → which
projections/lemmas/witnesses emerge → trace content and cost
(witness-level, never verdict-level), so per Q3 it ports: ~150
self-contained lines — `var_info_collector`/`reorder_lt`/
`heuristic_reorder`/`can_reorder`/`reorder`/`restore_order`/
`remove_learned_roots`/`reset_watches`/`reattach_arith_clauses`/
`sort_watched_clauses`/`sort_clauses_by_degree`, plus
`m_perm`/`m_inv_perm` and `pm.rename` as an MPoly-rename over the atom
table. Lands in 12c.6.

**State shape:** `Nlsat/Solver.lean`, untrusted.
`SolverM := StateM Solver`; `Solver.store : CellStore` + `liftC`
lifting CellM ops (store-era lessons apply: `modify`-style updates,
one SolverM computation per scenario in tests). Fields mirror imp:
assignment (`Assignment` from Evaluator.lean), atoms
(`Array (Option Atom)`), bvalues (`LBool` tri-state, new), levels,
justifications (new inductive: null/decision/clause id/lazy(lits,
clauseIds)), bwatches/watches (`Array (Array ClauseId)`), dead, isInt,
infeasible (`Array IntervalSet`), var2eq (bvar refs), clauses/learned
(append-only id tables; `del_clause` unreachable under the entry —
reorder fires pre-search when learned is empty), trail (5-constructor
inductive: bvarAssignment/infeasibleUpdt/newLevel/newStage/updtEq),
perm/invPerm, scopeLvl/stages/bk/xk, stats counters
(conflicts/propagations/decisions — `m_conflicts` gates
`m_max_conflicts=UINT_MAX`). `updt_eq` ported minus the
assumption-set gates (always-null under the entry; noted).
`is_full_dimensional` family lands with check() — the flag is stored
for 12d's `explain.set_full_dimensional`.

**Explain boundary:** `resolve` takes explain as an explicit
parameter `Array Literal → SolverM (Array Literal)`, pinned to
`nlsat_explain.h`@4.12.5's `operator()(num, lits, out)` (appends
projection literals; `resolve_lazy_justification` itself appends the
negated core). 12d supplies the real projection. Tests use a mock
(`pure #[]`) — which is also the faithful univariate behavior (no
lower vars ⇒ nothing to project), so univariate-conflict UNSAT pins
are real, not mock-dependent. Trace emission hooks land here unpinned
(standing rule 3).

**Option threading (29.5 ruling):** evaluator root paths return
`Option`; `value()` only runs with max_var assigned (z3 SASSERT), so
`none` is the z3-abort image. `value`/`check` thread `Option` —
`check : SolverM (Option LBool)`, `none` = z3's throw/SASSERT-abort,
never a silent default (F7 lesson).

**Seam fix in 12c.3:** z3's `infeasible_intervals(a, neg, &cls)`
stores the clause in each interval's justification
(`R_propagate`'s `get_justifications` reads `m_clause`); our
`infeasibleIntervals{Ineq,Root}` don't take it. Add an optional
`clauseId` parameter threaded to interval construction.

Slice plan (each lands compiling + pinned, small commits):

- **12c.1 scaffold** `todo`: LBool, Justification, TrailEntry, Solver
  record, SolverM + liftC; mk_bool_var/mk_var/register_var/
  mk_true_bvar; mk_ineq_literal/mk_root_atom (atom table); max_var /
  max_bvar / degree family; `lit_lt` (pure-bool-first, then max_var,
  then degree, then eq-last, then index — semantic: fixes
  first_undef selection order); mk_clause (sort + attach),
  attach/deattach watches. Pins: lit_lt order cases, watch attachment
  by max_var/max_bvar, atom/literal/clause construction.
- **12c.2 trail + undo + assign + value** `todo`: assign/decide/
  new_level/new_stage/updt_eq/save_*_trail + the undo_until_* family;
  assigned_value; value (assigned → bvalues, else evaluator when
  max_var assigned); is_satisfied(clause)/is_inconsistent. Pins:
  undo restores bvalues/levels/justifications/infeasible/var2eq/
  assignment bindings (CellStore refinements persist — store-era
  semantics); value() three-way; updt_eq degree ordering +
  justification-kind gates.
- **12c.3 propagation** `todo`: R_propagate (lazy jst carries core
  lits + clause ids), updt_infeasible, process_boolean_clause,
  process_arith_clause (the four infeasible-set cases verbatim:
  empty ⇒ propagate l; full ⇒ propagate ¬l; subset ⇒ propagate l with
  xk_set; union-full ⇒ propagate ¬l WITHOUT l in core
  (include_l=false)), unit ⇒ assign+updt, else decide+updt; m_lazy
  field ported (default 0). Clause-id seam (above). Pins per case
  incl. justification capture.
- **12c.4 search, SAT mode** `todo` (DESIGN's SAT-first): search loop
  (peek_next_bool_var/new_stage alternation, process_clauses over
  bwatches/watches, conflict → stub `pure none` until 12c.5),
  select_witness = pickInComplement (post-nla-32 anchor), is_satisfied
  (full), init_search. Acceptance: SAT instances (boolean-only,
  x²−2 > 0 ∧ x < 2, circle ∧ line, the re-anchored pick ladder
  shapes) with models VERIFIED BY EVALUATION (every input clause has a
  true literal under the model — z3's `check_satisfied` CASSERT made
  an external pin).
- **12c.5 resolve** `todo`: process_antecedent/resolve_clause×2/
  resolve_lazy_justification (explain param)/only_literals_from_
  previous_stages/max_scope_lvl/remove_literals_from_lvl/
  is_bool_lemma/find_new_level_arith_lemma/lemma_is_clause/resolve
  with the goto-start loop; learned clause creation; the two backjump
  cases (previous-stage vs decision-UIP); empty lemma ⇒ unsat.
  Pins: boolean-only conflicts (explain never called), univariate
  arith conflicts with mock-#[] explain (faithful, above), backjump
  level/stage targets, learned-clause reprocessing.
- **12c.6 reorder + check shell** `todo` (reorder port DECIDED by
  Danielle 2026-07-31): reorder block per the decision above;
  check()/search_check (real-valued; the integer branch-and-bound
  loop in search_check is the 12e seam — m_is_int exists but no B&B
  fires in 12c; declared slice boundary, NOT a divergence: 12e lands
  before any consumer); sort_watched_clauses;
  is_full_dimensional flag; stats. Pins: reorder permutes
  atoms/is_int/watches/assignment and restore_order round-trips
  (behavioral: same clauses, renamed vars), watch sorting by degree.

Acceptance (arc): 12c.4/12c.5 pins green, reorder round-trip green,
full build green, HANDOFF/BOARD updated. Estimate **4–6 sessions**
(board's earlier 2–4 predates the reorder promotion, the 4.12.5
re-anchor seam, and resolve being explicitly in-scope).

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
