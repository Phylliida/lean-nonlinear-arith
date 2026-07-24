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
- **nla-20** `todo` **Rule-correspondence spec.** The early artifact the
  containment proof actually needs: a source-referenced table mapping every
  Z3 nla generator to its Lean lemma family — nla_basics_lemmas.cpp schemas,
  order, monotonicity, tangent, divisions, monomial bounds, one row per rule,
  with the C++ provenance and the corresponding lemma statement. This document
  is the "Z3 ⊆ calculus" half of the structural argument (checked by reading,
  not running) and the fidelity contract nla-04/05 are built against.

## L1 — saturation layer

- **nla-04** `todo` Template lemma library: sign/zero/factorization, order,
  monotonicity, tangent-plane, division, monomial-bound schemas as parametric
  proven lemmas. (Source maps: nla_basics_lemmas, nla_order_lemmas,
  nla_monotone_lemmas, nla_tangent_lemmas, nla_divisions.)
- **nla-05** `todo` Monomial bookkeeping (emonics port: canonization up to
  sign/permutation) + generator loop instantiating nla-04 schemas.
- **nla-06** `todo` Linear leaf. **v0 decision: omega IS the leaf** — after
  monomial abstraction (each monomial -> fresh variable) the per-round closure
  check is a linear-ℤ problem, exactly omega's domain; no simplex needed until
  we want *models* to guide generation (Z3-style model-based lemma selection).
  v1 (only if blind saturation proves too slow on real corpora): untrusted
  exact-rational simplex (~300 lines meta) for models + Farkas certificates
  via linear_combination.
- **nla-07** `todo` Gröbner layer via grind ring engine / linear_combination,
  unthrottled. Re-run nla-03 corpus; expect most multiplicative-equality
  specimens to close here.

## Kernel + kit

- **nla-08** `todo` Computational Q[x] kernel (untrusted): dense ops, gcd,
  square-free decomposition, psc chains. Benchmark on specimen polynomials
  (perf derisk).
- **nla-09** `todo` Real algebraic numbers as (poly, isolating interval), sign
  determination emitting nla-02-style certified claims.
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

- **nla-12** `todo` nlsat search port (classic path of nlsat_solver.cpp /
  nlsat_explain.cpp; no levelwise). Emits traces in the 5-shape language
  (DESIGN.md section 2/L3) + integer branch splits.
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
