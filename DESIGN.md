# lean-nonlinear-arith — Design

Goal: a pure Lean library providing a `nonlinear_arith` tactic whose coverage is a
superset of Z3's nonlinear arithmetic as configured by Verus, built "the proper way":
every accepted goal gets a kernel-checked proof, and the completeness-critical layer
(nlsat) is handled by verified trace-checking rather than certificate formats that
can blow up (no SOS-as-coverage). End state: wired into tactus as the closer for
`by(nonlinear_arith)` goals, giving the structural guarantee that any codebase
verifying under Z3 verifies under the Lean backend at comparable cost.

Soundness is by construction throughout — the kernel checks every proof, and the
solver/search components are untrusted metacode. Every project risk is therefore a
coverage or performance risk, never a soundness risk.

## 1. What Z3 actually does (established by source reading, 2026-07-24)

Verus `by(nonlinear_arith)` queries run in a spun-off Z3 process with
`smt.arith.solver=6`, MBQI off. That engine is `nla_core::check`
(`z3/src/math/lp/nla_core.cpp:1285`), a pipeline of independent lemma generators,
each gated so it only runs when nothing upstream produced a lemma:

1. monomial interval propagation (`nla_intervals`, `monomial_bounds`)
2. pseudo-linear refinement
3. weighted round-robin: Horner-form interval lemmas / Gröbner (`nla_grobner`) /
   branching bounds
4. bounded nlsat (`max_conflicts=100`, adaptive delay)
5. sign/zero/factorization templates (`nla_basics_lemmas`)
6. division axioms (`nla_divisions`)
7. weighted round-robin: order / monotonicity / tangent-plane lemmas
8. full nlsat at level >= 2 (`nra_solver.cpp`, one-shot, no model priming)

Key structural facts:

- Every component except nlsat emits `lemma` objects (`nla_types.h:52`): a
  disjunction of *linear* inequalities over a monomial-extended vocabulary (each
  monomial gets a fresh variable), drawn from finite rule schemas. The scheduling
  heuristics only *select from* the closure of those schemas; they never extend it.
  Therefore an unthrottled Lean-side saturation over the same schemas covers every
  budgeted Z3 run, any version with the same rule set.
- nlsat is enabled for Verus queries: `arith.nl.nra` defaults to true and nothing in
  the solver-6 path reads the `smt.arith.nl=false` Verus sets globally (that flag
  only gates legacy solver 2; the param doc saying otherwise is stale).
- `nla_powers` (x^y) is unreachable from Verus (no exponentiation in emitted AIR).
  `nla_divisions` is reachable (Euclidean div/mod).
- verus-dev ships Z3 4.12.5, which predates nlsat's `levelwise` single-cell mode;
  current Z3 falls back to the classic projection when levelwise fails. The classic
  Jovanovic–de Moura projection is the spec.

Empirical sizing (verus-rational, nlsat amputated via `smt.arith.nl.nra=false`,
no cache, 2026-07-24): 692 verified / 39 errors. So ~1/7 of nonlinear call sites in
the most nonlinear-heavy foundational crate depend on the nlsat layer under Z3's
scheduling — and the failing goals are mostly multiplicative equalities under
hypotheses (Gröbner-shaped; Z3 throttles its Gröbner layer). The intrinsically
semialgebraic residue is smaller still. The cheap layers carry most of the load;
nlsat is a rarely-consulted capstone. (Numbers are a dated snapshot, not a pin.)

## 2. Architecture: three layers

### L1 — Saturation layer (faithful nla port)

A tactic implementing the lemma-generator pipeline with proofs:

- Template lemma library: the finite schemas from `nla_basics` / `nla_order_lemmas`
  / `nla_monotone_lemmas` / `nla_tangent_lemmas` / `nla_divisions` / monomial
  bounds, pre-proven as parametric Lean lemmas and instantiated by the generators.
- Monomial bookkeeping ported from `emonics.cpp` (canonization up to sign and
  permutation — this is where fidelity bugs would hide; port carefully).
- Gröbner layer: reuse grind's commutative-ring engine / `linear_combination`
  rather than porting Z3's PDD solver. Run unthrottled — this is expected to absorb
  most of the census failures that fell to nlsat under Z3's scheduling.
- Linear leaf: exact-rational simplex over the monomial-extended vocabulary
  (untrusted), returning models to drive generation and Farkas certificates on
  UNSAT, checked by `linear_combination`. Integer completion via omega on leaves.

L1 alone should make most real workloads green. It is also where run-cost parity
with Z3 comes from on the common path.

### L2 — nlsat search (untrusted metacode)

Port of the classic `nlsat_solver.cpp` / `nlsat_explain.cpp` path: model-constructing
search over real algebraic numbers with projection-based explanations. Computational
kernel: dense Q[x] arithmetic, gcd, square-free decomposition, psc (principal
subresultant coefficient) chains; real algebraic numbers as (defining polynomial,
isolating rational interval) pairs. All unverified — its only obligation is to emit
a trace whose steps the checker can discharge.

### L3 — Trace checker (the verified part)

The explanation language of `nlsat_explain.cpp` is exactly five shapes:

| # | shape | discharge |
|---|-------|-----------|
| 1 | sign atoms on projection polys (leading coeffs, psc chains of (p,p') and (p,q)) | kit theorem S1 |
| 2 | root atoms `y ~ root_i(p)`: deg 1 -> plain ineq; deg 2 -> Thom sign encoding (signs of B^2-4AC, 2Ay+B, p); deg >= 3 -> genuine root atom | trivial / S3 / S2 |
| 3 | cell-bracketing literals around the sample | S1 + S2 |
| 4 | pseudo-division sign transfer `lc(p)^d * h = q*p + r` + parity cases | per-instance `ring` |
| 5 | square-free factorization steps | per-instance `ring` |

Plus: integer branching (`x <= floor(v) \/ x >= ceil(v)`) interleaved for int
variables — LIA-checkable splits whose leaves are real-infeasibility traces.

## 3. The formalization kit

Everything instantiates at ℝ — mathlib's real analysis (IVT, Rolle, continuity,
connectedness) does the heavy lifting, and the absence of `RealClosedField` theory
in mathlib (checked Nov 2025: not even the definition) is dodged entirely. Cofactor
identities inside psc chains (Res = A*p + B*q and friends) certify per-instance by
`ring`, shrinking the abstract theory needed.

- **S1 (research kernel).** Projection soundness for the psc operator: on a
  connected region where the leading coefficients and the disc-chain/res-chain
  elements of a square-free family keep their signs, root counts and root orderings
  of the family are invariant (and hence sign patterns between roots). This is
  Collins-style delineability restricted to exactly the operator Z3 uses.
  Formalized nowhere, in any assistant; it is the reason verified multivariate CAD
  does not exist. Scoped here to one theorem family over ℝ with root-continuity +
  counting as ingredients.
- **S2. Certified root counting/isolation** for concrete rational polynomials:
  "p has exactly k roots in [a,b]", "q has constant sign on [a,b]", giving signs at
  algebraic points by evaluation at rational bracket endpoints. Reference
  implementation: Isabelle AFP (Sturm_Sequences, BKR). Possible mathlib-only
  shortcut to derisk first: IVT gives root lower bounds; a Rolle-chain argument
  (#roots(p) <= #roots(p') + 1, recursing down the derivative chain with sign
  evaluations) gives per-instance upper bounds without general Sturm theory.
- **S3. Thom quadratic lemma** (fixed, easy): root order/relation for degree-2
  determined by signs of discriminant, derivative, and value.
- **S4/S5.** Per-instance `ring` obligations — nearly free.
- **Resultant vanishing** (Res(p,q)=0 <-> common root, over ℂ descended to ℝ):
  mathlib-adjacent supporting theorem.

## 4. Design decisions

- **Search runs at Lean-checking time** (tactic execution), never at tactus
  emission. Emission stays syntactic and deterministic. Artifact caching gives
  pay-once economics. Optional later: `try this`-style output freezing a found
  trace into source as an explicit certificate term.
- **mathlib dependency** is accepted (ℝ, IVT, Rolle are non-negotiable for the kit;
  mathlib is pure Lean). Scope imports narrowly for build-time hygiene. The
  alternative (algebraic real closure of ℚ, no analysis) is noted and rejected as a
  far larger formalization.
- **Int goals relax to ℝ** at the front end (validity over ℝ implies validity over
  ℤ for the polynomial fragment); integer-specific reasoning stays with omega and
  branch splits.
- **Version pin:** classic projection path only (Z3 4.12.5 parity). Newer Z3
  optimizations (levelwise) affect constants, not coverage — both are complete
  decision procedures.
- **Layering:** L1 first, always; L2/L3 consulted only when L1 saturates without
  closing. Layers compose (`<;>` style), no exclusive gates.

## 5. Risk register (soundness is never at risk; these are coverage/schedule)

| risk | severity | derisk spike |
|------|----------|--------------|
| S1 statement doesn't stabilize (definitional choices: psc formulation, root ordering invariance, connectedness form) | high | write statement-only Lean file before anything else; discover mathlib gaps by forcing elaboration |
| S2 harder than expected in Lean (no Sturm anywhere in mathlib) | high | Rolle-chain + IVT spike on a concrete census specimen; fall back to general Sturm port (AFP as map) |
| L1 coverage overestimated (census failures need genuine semialgebraic reasoning, not just unthrottled Gröbner) | medium | extract the 39 census goals as Lean files; baseline against nlinarith/polyrith/grind before building anything |
| Lean metaprogram performance on Q[x]/algebraic-number kernels | medium | benchmark kernel ops on census-specimen polynomials early |
| mathlib version drift vs tactus toolchain | low | pin to v4.25.0 (matches local caches); revisit at integration |

## 6. References

- Jovanovic, de Moura: "Solving Non-linear Arithmetic" (IJCAR 2012) — the nlsat
  algorithm and the explain/projection function this library ports.
- `z3/src/nlsat/nlsat_explain.cpp` (1930 lines) — taxonomy source; key functions:
  `project` (:1087), `add_root_literal` (:824), `mk_quadratic_root` (:886, Thom),
  `psc_discriminant` (:782), `psc_resultant` (:803), pseudo-division rules
  (comment block at :1153).
- `z3/src/math/lp/nla_core.cpp:1285` — the lemma-generator pipeline (L1 spec).
- Isabelle AFP: Sturm_Sequences, BenOr_Kozen_Reif — reference implementations for S2.
- Cohen–Mahboubi (Coq): Tarski QE formalization — existence proof for the field,
  not a usable implementation.
- Census log: verus-cad session scratchpad 2026-07-24 (no-nra-run.log), wrapper
  trick: `VERUS_Z3_PATH` -> script exec'ing z3 with `smt.arith.nl.nra=false`.
