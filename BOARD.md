# BOARD — lean-nonlinear-arith

Entries live in `board/`, one file per item, in the original order.
Risk-first ordering: nla-01..03 are the derisk spikes and come before any
infrastructure investment. Status: `todo` / `active` / `done` / `blocked` /
`dropped`. See DESIGN.md for architecture and the risk register.

## Derisk spikes (do first, in any order, all cheap relative to what they retire)
- [nla-00 `done` Repo + Lake scaffolding, mathlib v4.25.0 pin, library layout.](board/nla-00-repo-lake-scaffolding.md) `done`
- [nla-01 `done` S1 statement spike. `Projection/S1Statement.lean`](board/nla-01-s1-statement-spike-projection.md) `done`
- [nla-02 `done` Root-counting spike (S2-lite). `RootCounting/Spike.lean`,](board/nla-02-root-counting-spike-rootcounting.md) `done`
- [nla-03 `done` (descoped by design decision 2026-07-24). The project is](board/nla-03-descoped.md) `done`
- [nla-20 `done` (2026-07-24, RULES.md — 39 emission sites rowed, all](board/nla-20-rule-correspondence-spec.md) `done`

## L1 — saturation layer
- [nla-04 `done` (2026-07-24) Template lemma library:](board/nla-04-template-lemma-library.md) `done`
- [nla-05 `done` (2026-07-25; hardening follow-ons live in nla-21..23)](board/nla-05.md) `done`
- [nla-06 `todo` Linear leaf. v0 decision: omega IS the leaf — after](board/nla-06-linear-leaf-v0-decision.md) `todo`
- [nla-07 `done` (2026-07-25) Gröbner layer via grind's ring engine, per](board/nla-07-grobner-layer-via-grind.md) `done`
- [nla-07b `todo` Gröbner→saturation propagation. Z3's](board/nla-07b-grobner-saturation-propagation.md) `todo`

- [Standing directive: source-fidelity over empirical confirmation](board/standing-directive-source-fidelity-over-empirical.md)

## L1 hardening (from the 2026-07-25 code review; directives from Danielle)
- [nla-21 `todo` Shared atom space for noted facts. The right fix for](board/nla-21-shared-atom-space-for.md) `todo`
- [nla-22 `todo` Dependency work-queues, Z3-identical. Replace the](board/nla-22-dependency-work-queues.md) `todo`
- [nla-24 `active` Kernel/oracle correctness lemmas (2026-07-26).](board/nla-24-kernel-oracle-correctness-lemmas.md) `active`
- [nla-23 `todo` q-formula optimality proofs. The D4/D5 quotient](board/nla-23-q-formula-optimality-proofs.md) `todo`

- [nla-25 `partial` — L2 kernel correctness upgrades (directives from Danielle, 2026-07-26)](board/nla-25-l2-kernel-correctness-upgrades.md) `partial`
- [nla-26 `done` (2026-07-26 eve) — fidelity hardening: divergence elimination (Danielle, 2026-07-26)](board/nla-26-fidelity-hardening-divergence-elimination.md) `done`
- [nla-27 `done` (2026-07-28) — univariate ℤ factorization (default-Z3 parity; Danielle, 2026-07-26 review)](board/nla-27-univariate-z-factorization.md) `done`
- [nla-28 `done` (2026-07-28) — anum statefulness threading (Danielle, 2026-07-26 review; sequence BEFORE/WITH 12…](board/nla-28-anum-statefulness-threading.md) `done`

## Kernel + kit
- [nla-08 `done` (2026-07-25) Computational ℚ[x] kernel (untrusted),](board/nla-08-computational-q-x-kernel.md) `done`
- [nla-09 `done` (2026-07-26) Real algebraic numbers as (poly, isolating](board/nla-09-real-algebraic-numbers-as.md) `done`
- [nla-10 `todo` General Sturm theory — only if nla-02 says per-instance](board/nla-10-general-sturm-theory-only.md) `todo`
- [nla-11 `todo` S1 proof campaign. The long pole; two independent](board/nla-11-s1-proof-campaign-the.md) `todo`
- [nla-19 `todo` Quadratic-complete checker (S1-free). Sequencing](board/nla-19-quadratic-complete-checker-sequencing.md) `todo`

- [nla-29 `done` — anum arithmetic (eval/mul/inv/div) for the q≡0 fallbacks (Danielle, 2026-07-28; closed 2026-07…](board/nla-29-anum-arithmetic-for-the.md) `done`
- [nla-31 `todo` — termination proofs for the analytic walks/loops (Danielle, 2026-07-31)](board/nla-31-termination-proofs-for-the.md) `todo`
- [nla-30 `todo` — general multivariate resultant (deferred; Danielle 2026-07-31)](board/nla-30-general-multivariate-resultant.md) `todo`
- [nla-32 `done` (2026-07-31) — 4.12.5 re-anchoring audit (found in the 12c planning sweep, 2026-07-31)](board/nla-32-4-12-5-re-anchoring-audit.md) `done`
- [nla-12d design review `done` (2026-08-01, Danielle-requested, post-12d.6a)](board/nla-12d-design-review.md) `done`
- [nla-12d `active` (opened 2026-08-01) — explain: the projection port](board/nla-12d-explain-the-projection-port.md) `active`
- [nla-19a `active` (opened 2026-08-01) — checker v0 + Q1 coverage proof (12d twin)](board/nla-19a-checker-v0-q1-coverage.md) `active`
- [nla-19a design review 2 `done` (2026-08-03, post-session-1, Danielle-approved R1–R9)](board/nla-19a-design-review-2.md) `done`
- [nla-19a progress log (2026-08-03, session 1 of the arc)](board/nla-19a-progress-log.md)
- [nla-19a Slice E/F sub-slice plan (2026-08-06, planning session)](board/nla-19a-slice-e-f-sub.md)
- [nla-19a design review 3 `done` (2026-08-06, mid-F/G arc — parity + regret lenses; R1'/R2' Danielle-approved sa…](board/nla-19a-design-review-3.md) `done`
- [nla-19a design review 4 `done` (2026-08-06, pre-F2; R-i–R-viii Danielle-approved same day)](board/nla-19a-design-review-4.md) `done`
- [nla-19a design review 5 `done` (2026-08-07, pre-F2-step-collection; probe-driven; decisions resolved by Daniel…](board/nla-19a-design-review-5.md) `done`
- [nla-19a design review 7 `done` (2026-08-09, post-F4; Danielle-requested; boundary probes + z3 re-read)](board/nla-19a-design-review-7.md) `done`
- [Checker-completeness gap inventory (2026-08-09, consolidated at Danielle's request)](board/checker-completeness-gap-inventory.md)
- [G4 census slice — status + findings (2026-08-10, iteration 1)](board/g4-census-slice-status-findings.md)
- [nla-19a design review 15 `done` (2026-08-10; G4 census slice COMPLETE — items 3/4 + audit)](board/nla-19a-design-review-15.md) `done`
- [nla-19b plan `done` (2026-08-10, pre-implementation planning sweep — pseudoDivision → M3; all four slices landed 2026-08-13)](board/nla-19b-plan.md) `done`
- [nla-19b Slice 0 `done` (2026-08-10) — simplify-cluster live recon + the o139 search divergence](board/nla-19b-slice-0-simplify-cluster.md) `done`
- [nla-19b Slice 0 addendum (2026-08-10 eve): the o139 divergence RESOLVED — `Explain.project` todo writeback bug](board/nla-19b-slice-0-addendum-the.md)
- [G11 lane `done` + o139 walked END-TO-END (2026-08-11) — the broken-tree session closed out](board/g11-lane-o139-walked-end-to.md) `done`
- [G11 close-out design review `done` (2026-08-11 eve; Danielle-requested divergence/regret audit of the G11 clos…](board/g11-close-out-design-review.md) `done`
- [nla-19b Slice 1 `done` (2026-08-13) — grammar + identity close + sign-transfer family; the closeAlgRefl HOLE b…](board/nla-19b-slice-1-grammar-identity.md) `done`
- [nla-19b Slice 1 design review `done` (2026-08-13, Danielle-requested; post-Slice-1 divergence/regret audit)](board/nla-19b-slice-1-design-review.md) `done`
- [nla-19b Slice 2 `done` (2026-08-13) — Refute consumption: rebuilt-literal equivalence transport + drop lane](board/nla-19b-slice-2-refute-consumption.md) `done`
- [nla-19b Slice 2 design review `done` (2026-08-13 eve, Danielle-requested; post-Slice-2 divergence/regret audit…](board/nla-19b-slice-2-design-review.md) `done`
- [nla-19b Slice 3 `done` (2026-08-13) — isV0 gate lift + pd1 acceptance walked; **M3 DECLARED**](board/nla-19b-slice-3-gate-lift.md) `done`
- [nla-19b Slice 3 design review `done` (2026-08-13; divergence/regret audit — R-iii pd-binary-differential + R-iv intBranch grammar boarded)](board/nla-19b-slice-3-design-review.md) `done`
- [nla-12e plan `done` (2026-08-13, planning sweep — G6 integer B&B; decisions 1–2 Danielle-resolved same day)](board/nla-12e-plan.md) `done`
- [nla-12e `done` (2026-08-13, ONE session) — integer B&B ported end-to-end; G6 closed; isV0 := !isS1Gated (last shape gate lifted)](board/nla-12e-done.md) `done`
- [nla-14 plan `active` (2026-08-13 eve, planning sweep — the `nonlinear_arith` tactic; decisions 1–5 RESOLVED by Danielle's standing principles incl. performance-parity: full Boolean structure via TSEITIN proxies (z3's mechanism; bool vars already ported search-side, checker-side `Atom.bool` + BoolForm reflection is the new trusted component), SAT-model display in scope)](board/nla-14-plan.md) `active`
- [nla-14 Slice 1 `done` (2026-08-13 eve) — Tseitin proxy checker support: `Atom.bool` + `BoolDef`, interp/litHolds arms, taut/conseq reflection; additive, axioms clean](board/nla-14-slice-1-booldef-proxy-checker.md) `done`
- [nla-14 Slice 1 design review `done` (2026-08-13 eve, Danielle-requested) — R-i REAL (flattened defs struck → hierarchical, fuel-bounded; fixed same-day), R-ii Slice-2 refinement (top-proxy unit roots — no big truth tables), R-iii ite→opaque var (z3-faithful non-goal), R-iv representation re-confirmed; D-1/D-2 boarded](board/nla-14-slice-1-design-review.md) `done`
- [nla-19a design review 8 `done` (2026-08-09, post-G1/G2/G3; Danielle-requested gap audit)](board/nla-19a-design-review-8.md) `done`
- [nla-19a design review 9 `done` (2026-08-09; Danielle-requested: can R-a/R-b/R-c be fixed to full z3 parity?)](board/nla-19a-design-review-9.md) `done`
- [nla-19a design review 10 `done` (2026-08-09; R-a FULL — Danielle's standing directive: cover ALL cases, never …](board/nla-19a-design-review-10.md) `done`
- [nla-19a design review 12 `done` (2026-08-10; R-e FIXED — zero-product closes inside Or-split branches)](board/nla-19a-design-review-12.md) `done`
- [nla-19a design review 13 `done` (2026-08-10; Danielle-requested z3-divergence audit of review 12)](board/nla-19a-design-review-13.md) `done`
- [nla-19a design review 14 `done` (2026-08-10; Danielle: "is every known gap covered by a boarded item?" — R2' F…](board/nla-19a-design-review-14.md) `done`
- [nla-19a design review 11 `done` (2026-08-09; Danielle-requested audit of review 10: nothing deferred, no uncov…](board/nla-19a-design-review-11.md) `done`
- [nla-19a design review 6 `done` (2026-08-09, post-F3; Danielle-requested; probes + adversarial re-read)](board/nla-19a-design-review-6.md) `done`
- [nla-12c design review `done` (2026-07-31, Danielle-requested, post-close)](board/nla-12c-design-review.md) `done`
- [nla-12c `done` (2026-07-31, same day as the spec) — the solver loop](board/nla-12c-the-solver-loop.md) `done`

## L2/L3 — nlsat
- [nla-12 `active` (lane opened 2026-07-26; slice plan + module map +](board/nla-12.md) `active`
- [nla-13 `todo` Trace checker: discharge shapes 4/5 by per-instance ring,](board/nla-13-trace-checker-discharge-shapes.md) `todo`
- [nla-14 `todo` Front-end tactic `nonlinear_arith`: Int -> Real relaxation,](board/nla-14-front-end-tactic-nonlinear.md) `todo`

## Integration
- [nla-15 `todo` tactus closer wiring: emit `nonlinear_arith` for](board/nla-15-tactus-closer-wiring-emit.md) `todo`
- [nla-16 `todo` Parity harness: run the full workspace nonlinear corpus](board/nla-16-parity-harness-run-the.md) `todo`

- [Milestone ladder (proof-first)](board/milestone-ladder.md)
