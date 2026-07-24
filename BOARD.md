# BOARD — lean-nonlinear-arith

Risk-first ordering: nla-01..03 are the derisk spikes and come before any
infrastructure investment. Status: `todo` / `active` / `done` / `blocked` /
`dropped`. See DESIGN.md for architecture and the risk register.

## Derisk spikes (do first, in any order, all cheap relative to what they retire)

- **nla-00** `done` Repo + Lake scaffolding, mathlib v4.25.0 pin, library layout.
- **nla-01** `todo` **S1 statement spike.** Statement-only Lean file for psc
  projection soundness (delineability): define psc chains over `Polynomial ℝ`
  (or via mathlib's resultant machinery where it exists), state sign-invariance =>
  root-count/order invariance on connected sets. No proofs — the goal is forcing
  the definitional choices and discovering mathlib gaps. Retires the highest risk.
- **nla-02** `todo` **Root-counting spike (S2-lite).** For one concrete census
  specimen polynomial: prove "exactly k roots in [a,b]" using IVT (lower bound) +
  Rolle-chain on derivatives (upper bound), mathlib only. Decides whether general
  Sturm theory is needed or per-instance certificates suffice.
- **nla-03** `todo` **Specimen corpus + baseline.** Extract the 39 census failures
  (verus-rational, no-nra run 2026-07-24) as standalone Lean goals. Baseline:
  how many close with existing tools (nlinarith, polyrith, grind, omega)?
  Calibrates how much L1 must deliver and what the true nlsat residue is.

## L1 — saturation layer

- **nla-04** `todo` Template lemma library: sign/zero/factorization, order,
  monotonicity, tangent-plane, division, monomial-bound schemas as parametric
  proven lemmas. (Source maps: nla_basics_lemmas, nla_order_lemmas,
  nla_monotone_lemmas, nla_tangent_lemmas, nla_divisions.)
- **nla-05** `todo` Monomial bookkeeping (emonics port: canonization up to
  sign/permutation) + generator loop instantiating nla-04 schemas.
- **nla-06** `todo` Linear leaf: exact-rational simplex (untrusted) over
  monomial-extended vocabulary; Farkas certificates checked by
  linear_combination; omega on integer leaves.
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
- **nla-11** `todo` **S1 proof campaign**: root continuity, counting arguments,
  psc semantics, the delineability theorem. The long pole; start once nla-01
  stabilizes the statement.

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
  `by(nonlinear_arith)` sites; toolchain/version alignment.
- **nla-16** `todo` Parity harness: run the full workspace nonlinear corpus
  through the tactic; compare against Z3 site-for-site; census-style report.
  Acceptance: no site that Z3 closes and we don't.
