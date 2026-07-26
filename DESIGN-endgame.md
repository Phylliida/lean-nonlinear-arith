# DESIGN-endgame — completion spec for lean-nonlinear-arith

*2026-07-26, written at the close of the nla-26 fidelity arc + 25.4 order
theorems. This is the single document that specs everything remaining to
finish the subproject, with all decisions and source anchors gathered in
one place. Board items stay the unit of execution; this doc is the map.*

---

## 0. Finish line

**The goal (Danielle, 2026-07-24):** structural guarantee that every
Z3-verifying codebase verifies under tactus/Lean untweaked — 100%
coverage, "the proper way": no SOS-as-coverage shortcut, verified
nlsat trace-checking at matching cost.

**Definition of done, two tiers:**

- **Tier A (M3+M5-quadratic+M6):** the `nonlinear_arith` tactic ships
  with L1 saturation (done) + quadratic-fragment nlsat search/check.
  Every `by(nonlinear_arith)` site whose trace stays at per-variable
  degree ≤ 2 closes verified; the containment writeup covers L1
  rule-for-rule and the checker end-to-end. The parity harness (nla-16)
  reports **zero sites that Z3 closes and we don't** across the
  workspace corpus, within the agreed budget. Verus goals are
  overwhelmingly in-fragment, so Tier A is expected to BE workspace-100%;
  the harness confirms.
- **Tier B (M4/M5 full):** the S1 campaign (nla-11, plus nla-10 if
  needed) removes the fragment restriction — full-degree Collins
  projection checking. This is what makes the guarantee structural
  rather than empirical for arbitrary future code.

**Trust surface note (what the guarantee actually rests on):** only the
trusted layer — `Templates/*`, `Certificates/{Defs,Sound}`, the S3
quadratic kit, the 19a/b discharge lemmas, and the final tactic glue.
Everything in `Kernel/`, `Nlsat/`, `Tactic/Oracle` is untrusted search:
a bug there costs completeness (a failed certification), never
soundness. The proof-layer program (§5) is defense-in-depth and
completeness insurance, not a soundness prerequisite.

---

## 1. Position (2026-07-26)

Done and green (all sorry-free, full build 7575 jobs):

| Layer | Items | State |
|---|---|---|
| L1 saturation | nla-01..05, 07, 20, 24-partial, 26 | **complete** — 112+ tests, RULES.md 27/27 rows, parity audited row-by-row |
| Kernel | nla-08 (QPoly), nla-09 (roots + trusted certs), Mpbq, RAlg mini-anum | **complete**, perf derisked |
| nlsat lane | 12a (Types/IntervalSet), 12b-i (AnumEval), S3 Thom kit, nla-26 fidelity arc, F1–F7 review, 25.4 order theorems | **complete** |
| Remaining declared divergences | Sturm-vs-Descartes isolation; QPoly ℚ[x] kernel (bridged at `ofQPoly`); root-represented rationals at shared endpoints; no factorization (= `factor=false` parity → nla-27) | tracked |

Open: nla-28, 12b-ii, 12c, 12d, 19a, 19b, 12e, 13, 14, 15, 16 (critical
path); 27 (fidelity); 21, 22, 07b, 06 (L1 hardening); 23, 24-residual,
25-residual, 10, 11 (proof layer / S1).

---

## 2. Critical path to Tier A

Ordering: **28 → 12b-ii → 12c → 12d+19a (same arc) → 19b → 12e → 14 →
15 → 27 → 16.** Rationale per item below.

### 2.1 nla-28 — anum statefulness threading *(next up; ~1 session: ½ design + ½ signatures/implementation)*

**Problem (F3, probe-confirmed reading):** Z3's anum ops mutate their
operands and the refinement persists — `compare`/`select`/`separate`
take `numeral&`; `int_gt`/`int_lt` even `const_cast` refinement into
interval-set endpoints stored behind const pointers
(`algebraic_numbers.cpp:2830`). Our pure ports discard that work, so
later magnitude gates and select-niceness decisions see WIDER intervals
than Z3 at the same program point — behavioral divergence (witness
drift), not just performance.

**Mutation sites to thread (complete list from source):**
1. the solver assignment `x2v` — evaluator calls refine assigned cells
   (`eval_sign_at` interval pass, `isolate_roots` filtering);
2. interval-set endpoint cells — `pick_in_complement`'s
   `int_gt`/`int_lt`/`select` refine endpoints of the *stored* set;
3. explain-side compares during cell construction.

**Design (recommended; confirm before implementing):** two levels.
- RAlg level: every refining op returns its refined argument(s)
  alongside the result — `compare : RAlg → RAlg → (Ordering × RAlg ×
  RAlg)`, `intGt : RAlg → (Int × RAlg)`, etc. (the F3-boarded shape).
  No monads at this level; tuples keep the ports diffable against
  source.
- Solver level (12c): the assignment map `Var → RAlg` is the single
  authoritative store, updated after every evaluator/compare call;
  `IntervalSet` values are rebuilt with refined endpoints on return
  from `pickInComplement` / endpoint comparisons (persistent-structure
  analogue of z3's in-place endpoint mutation).

**Acceptance:** a pin where pure-vs-threaded *differ*: construct a cell
pair where `select` after an earlier `intGt` refinement returns a
dyadic-nicer witness than the unrefined intervals would; assert the
z3-shaped (threaded) result. Existing RAlg/IntervalSet suites re-green
under new signatures.

### 2.2 nla-12b-ii — evalSignAt + isolateRootsAt assembly *(1–2 sessions)*

Spec is fully written: DESIGN-nlsat-quadratic §4b (three entry points,
from `algebraic_numbers.cpp:2246/2547/2902`). Build on nla-28
signatures. Note §4b's "declared divergences" block was superseded by
nla-26 — dyadic endpoints, refine rationality discovery, and binary
magnitude gating are all now faithful (block corrected in place).

Remaining content beyond §4b's text:
- `q ≡ 0` fallbacks in `isolateRootsAt`: linear-coefficient solve, else
  the auxiliary-variable (`z·x^i + …`) nested elimination path;
- evaluator surface consuming them: `sign_table` + `infeasible_intervals`
  (`nlsat_evaluator.cpp:494/599`) — per-atom infeasible interval sets
  under the partial model, with justification literals, feeding 12c
  propagation;
- the signs variant (:2902): refine roots to `DEFAULT_PRECISION`, then
  `eval_sign_at` at `int_lt`/`select`/`int_gt` sample points between
  consecutive roots (these are exactly the nla-26.4 witness entry
  points — reuse, don't duplicate).

**Tests:** √2/φ/cbrt2 sign pins under partial assignments; isolation
under assignment vs direct QPoly isolation on rational cells
(differential); zero-poly and degenerate-`q` fallback pins; sign_table
vs brute-force sampling differential on a probe grid.

### 2.3 nla-12c — Solver loop *(2–4 sessions; the big port)*

Faithful classic search of `nlsat_solver.cpp` (4.12.5, no levelwise, no
MBQI, `randomize=false` pinned): stage/level structure keyed on max_var,
boolean + arithmetic decisions, propagation via infeasible-interval
sets with justification literals, `select_witness` =
`pickInComplement`, conflict resolution calling explain (12d),
backjumping, learned clauses.

**Locked:** SAT mode first — models found are *verified by evaluation*
(the evaluator is its own checker for sat answers; cheap correctness
signal before the conflict path exists). Then the conflict path.

**Scope decisions to make at port time (flag now, decide against
source):** clause-learning minimization and restart policy affect WHICH
lemmas/traces emerge, so per the parity directive they are semantic —
port them exactly, do not approximate. Anything that provably only
*selects* from the same closure (activity heuristics order) may be
simplified only with an explicit parity argument in the commit, same
discipline as L1.

**State shape:** solver state owns the assignment store from nla-28;
trace emission hooks land here but payloads stay unpinned until 12d/19a
consume them (standing rule).

### 2.4 nla-12d + nla-19a — Explain + Checker v0, same arc *(3–4 sessions combined)*

These two are deliberately one arc: trace payloads get pinned only when
the checker consumes them.

**12d — `Nlsat/Explain.lean`:** classic projection restricted to the
fragment (`nlsat_explain.cpp`): `project()` with `ensure_sign` on
lcs/psc-chain elements, root atoms via `mk_linear_root` /
`mk_quadratic_root` incl. the degenerate-A `mk_plinear_root` fallback
with its `ensure_sign` assumption on the linear coefficient (:854–919),
`add_cell_lits` around the sample, pseudo-division sign-transfer steps,
square-free steps (factor=false today; nla-27 adds factor hooks).
Fragment gate: **degree ≤ 2 in the top variable at every projection
step**, checked at explain time; out-of-fragment aborts the trace (the
search remains usable as a model-finder/disprover). Emits the 8-shape
trace language (DESIGN-nlsat-quadratic §2).

**19a — `Nlsat/Check.lean` v0:** discharge map per
DESIGN-nlsat-quadratic §3: `leafNumeric` → nla-09 certificates
(`check*_sound (by decide)`); `thomQuadratic` → S3 kit;
`linearRoot` → plain inequality lemmas; `cellBound` → the S3 4-lemma
point-vs-root ordering family + linarith glue.

**Q1 (the open question on the board, resolve here):** does the finite
S3 ordering family + linarith cover ALL emitted cell shapes? Plan:
empirical first — run 12d on hand goals + the first census rows, censor
the emitted cell-literal shapes, check each against the family; if the
enumeration closes, prove the coverage lemma (cell shapes are generated
by a finite grammar — this should be a small case analysis, not a
research item); if it doesn't close, extend the S3 family (same
Templates/Quadratic style) before writing the coverage lemma.

**Acceptance:** end-to-end on hand goals with algebraic cells (√2-grade),
negative probes (corrupted trace rejected), and the first
search→trace→checked-theorem round trip.

### 2.5 nla-19b — full checker glue *(1–2 sessions)*

`pseudoDivision` (per-instance ring identities + parity cases),
`factorSplit`, resolution glue between checked steps. End-to-end target:
a census-shaped goal through search → trace → checked theorem.
`ordering_139` (the L1-open specimen, degree-3 cross products) is the
standing target *if* its trace stays in fragment; else the first fully
quadratic census row. This lands **M3**.

### 2.6 nla-12e — integer branching + Int frontend *(1–2 sessions)*

Verus VCs are ℤ; nlsat is ℝ. Port z3's integer handling for the nlsat
path: branch-and-bound splits (`x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉` at non-integer
witnesses) as trace steps — checker-side each split is an omega-trivial
disjunction, so this is search-side work almost entirely. Confirm
against source where solver-6 does the splitting for the nra path
(nra_solver.cpp / nlsat's mk_branch analogue) and port that exact
policy. L1 already owns div/mod semantics (RULES rows); L2 sees
polynomial atoms only — assert this invariant at the frontend boundary.

### 2.7 nla-14 — the `nonlinear_arith` front-end tactic *(1–2 sessions)*

- Layering: L1 `nla_saturate` first (fast path, most goals), on failure
  L2/L3 search+check. Budgets per the BUDGET-SHAPE lesson:
  `withLayerHeartbeats` (fresh user budget per layer, Z3-per-module
  analogue) — never fraction-of-remaining.
- Int → Real atom mapping + 12e branching for integer goals; ℤ ⊆ ℝ
  relaxation direction is sound for proving (goal proven over ℝ with ℤ
  atoms specializes); div/mod never reach L2 (L1-owned).
- Hypothesis selection: Verus query shape — context-free, only stated
  `requires` (matches the spinoff query Z3 sees; no ambient-context
  mining beyond what L1 already does).

### 2.8 nla-15 — tactus closer wiring *(½ session)*

Emit `nonlinear_arith` for `by(nonlinear_arith)` sites in the tactus
Lean backend. Toolchain already aligned (identical lean+mathlib v4.25.0
pins); integration is a `require` line + closer-string emission +
crate-local check.sh gate. No design content remaining.

### 2.9 nla-27 — univariate ℤ factorization *(3–5 sessions, own arc; AFTER 19b e2e, BEFORE 16)*

Board entry is the spec (port `upolynomial_factorization.cpp` ~1300
lines: square-free factorization, Berlekamp over Z_p with prime trials
per `factor_max_prime`/`factor_num_primes`, lifting + recombination per
`factor_search_size`; wire into `RAlg.isolateRoots` per
`am::isolate_roots` :605). Consequences to land WITH it: `minimal` flag
on cells; `compareCore` minimal-branch (refine-until-disjoint) becomes
the common path and must be implemented; became-basic goes radical-only
(F1 guard becomes pure safety net); eager rational-root discovery.

**Sequencing rationale:** get the quadratic pipeline e2e green under
`factor=false` parity first (a legitimate z3 configuration — one flag),
then flip to default parity before the harness, since factor changes
witness shapes and code-path reachability (the F1 finding). Expect to
re-pin select/compare behavioral suites under factor=true (rational
roots become basic at construction — several nla-26 pins will change
values; that is fidelity working, not breakage — re-derive each from
source when it happens).

### 2.10 nla-16 — parity harness *(1–2 sessions + fallout budget)*

Run the full workspace nonlinear corpus through the tactic;
site-for-site comparison against Z3; census-style report.
**Acceptance gate: no site that Z3 closes and we don't.** Also the one
declared-empirical residue: budget/pacing confirmation (if pacing
drifts, first suspect is `intervalMagnitude`'s verbatim-quirk formula —
F6 note). Timing discipline: check `uptime` before trusting any
wall-clock numbers (standing lesson). M6 closes here: the harness
confirms coverage, it does not define it.

---

## 3. L1 hardening (parallel-safe, not on the critical path)

These four close the remaining L1 divergences-in-kind. None block M3;
all block calling L1 "port-complete" for M5's writeup.

- **nla-07b — faithful meta-Buchberger** *(2–3 sessions)*: port
  `nla_grobner`'s FIVE consumers (conflict / fixed / factorization /
  gcd_test / quotients) with cofactor tracking; note derived equalities
  whose monomials are collected atoms; certify via `linear_combination`
  with delaborated cofactors (or grind-discharge); demote `grind` to
  auxiliary. Standing directive: source-fidelity over
  equivalent-engine+empirical-check; the octagon port is the template.
- **nla-22 — Z3-identical dependency work-queues** *(1–2 sessions)*:
  port the todo-list structure from `nla_core`/`monomial_bounds`
  verbatim; kills the +54% fixpoint-confirmation overhead AND closes
  the scheduling-identity gap.
- **nla-21 — shared atom space** *(1 session)*: per-fact `ring_nf`
  normalization through one meta entry point for noted facts, appended
  `ms` spellings, and clause-phase instantiations (design constraints
  a/b/c already mapped on the board).
- **nla-06 — simplex model over Oracle** *(1–2 sessions)*: feasible
  ℚ-point over the oracle's constraint system; unlocks model-based
  clause relevance, model-anchored D4/D5/M/T tightness, and the O2/O3
  residual (O4 evars already done in oracle v1).

---

## 4. Proof-layer program (defense-in-depth; Danielle-directed)

**Cheap tier** (each ≤ 1 session; do opportunistically between arcs):
- `evalRat` homomorphism lemmas for `MPoly.add/neg/mul` (new, from the
  25.4 review — pins semantic correctness of the ported arithmetic,
  currently covered only by behavioral tests);
- `substRat`/`ofQPoly`/`coeffsIn` canonicity (extends 25.4's Canon
  preservation to the remaining constructors);
- `gradedLexCompare` order theorems (25.4-style; matters for 12b-ii's
  leading-monomial scans);
- `detMPoly` = spec determinant (Laplace layer, self-contained);
- `compareCore` cheap-half ("shared root in both open isolating
  intervals ⇒ equal", from root uniqueness — no Sturm);
- nla-23 q-formula attainment lemmas (exact interval optima — stronger
  than Z3 proves for itself);
- nla-24 residuals: `propagate` sup-loop characterization, Yun
  `∏ aᵢ^i` reconstruction.
- 25.4 polish: weaken `MPoly.mul_canon` to element-conditions on `p`;
  move `denseCompare`/`varBound` proof scaffolding out of the port
  namespace.

**Medium:** nla-24's `QPoly.psc = S1Statement.psc` bridge (determinant
identity; today true by construction-mirroring).

**Subprojects:**
- **nla-10 — Sturm correctness (S2)** *(multi-session; AFP
  Sturm_Sequences as the map; upstream-worthy)*. Gates: the counting
  half of compare trust, `rootFreeOn` completeness, and trace shapes
  1/3 at degree ≥ 3. Not needed for Tier A (quadratic checker is
  Sturm-free on the trusted side — nla-09 certificates carry the leaf
  trust).
- **nla-11 — S1 campaign** *(the long pole; research-grade)*: 11a
  resultant vanishing (Res=0 ↔ common root; Sylvester kernel ↔ Bezout;
  ℂ then descend — also the semantic consumer for `resultantElim`);
  11b psc ↔ gcd-degree correspondence (subresultant theory, biggest
  algebra piece); 11c continuous dependence of roots (Rouché or
  elementary compactness); 11d topological glue (constant count +
  continuity + connectedness ⇒ ordered continuous root functions = the
  Delineation). Tracks 11a/11c are independent and parallelizable.
  Estimate honestly uncertain: 10–20 sessions across all four.

---

## 5. M5 — the containment writeup

A repo document (not code) assembling the guarantee end to end:
1. per-rule fidelity — the RULES.md 27-row table + generator coverage
   audit (done, cite);
2. saturation completeness — L1 instantiates every reachable emission
   at least as strongly as Z3 (parity directive discharged row-by-row;
   scheduling-identity via nla-22);
3. RCF trace checking — checker soundness (trusted lemmas) +
   fragment-coverage statement (Q1's enumeration lemma) + the Tier B
   S1 path for the general case;
4. declared divergences appendix — the complete list with why each is
   witness-level only (never verdict-level).

*(≈1 session once M3 lands; update after 27 and after S1.)*

---

## 6. Open questions for Danielle

- **Q1 (19a):** S3 family coverage — plan is empirical-then-lemma
  (§2.4). OK to defer the coverage lemma until real traces exist?
- **Q2 (28):** threading shape — explicit refined-arg returns at RAlg +
  solver-state store at 12c (§2.1). Confirm before signatures land.
- **Q3 (12c):** confirm clause-learning minimization + restart policy
  are ported exactly (parity directive reading: they shape which traces
  emerge, so yes). Any z3 heuristic we're allowed to simplify needs a
  written parity argument.
- **Q4 (27):** sequencing after 19b / before 16 (§2.9), accepting that
  a batch of nla-26 behavioral pins get re-derived under factor=true.
- **Q5 (proof layer):** cheap tier opportunistically between arcs
  (recommended) vs batched at the end?
- **Q6 (16):** define "matching cost" acceptance concretely — proposal:
  per-site heartbeat budget with the layered `withLayerHeartbeats`
  shape, reported as a census table; no wall-clock gates (load
  unreliability).
- **Q7 (M4 timing):** start S1 (nla-11a/11c tracks parallelize with the
  12c/12d ports) opportunistically, or hold until Tier A ships?

## 7. Estimates and shape of the remainder

Critical path to Tier A: **~12–18 sessions**
(28: 1 · 12b-ii: 1–2 · 12c: 2–4 · 12d+19a: 3–4 · 19b: 1–2 · 12e: 1–2 ·
14: 1–2 · 15: ½ · 27: 3–5 · 16: 1–2, some overlap).
L1 hardening: +5–8 parallel-safe. Proof layer cheap tier: +3–5
opportunistic. Tier B (S1 + nla-10 + nla-13 general + M5 update):
+12–25, research risk concentrated in 11b.

Dependency skeleton:

```
28 → 12b-ii → 12c → 12d ⇄ 19a → 19b → 12e → 14 → 15 → 16
                                  ↑              27 ↗
        21,22,07b,06 (parallel)   S1: 11a ∥ 11c → 11b → 11d → 13 → M5-full
        proof-layer cheap tier (between arcs)
```

## 8. Standing directives that govern all remaining work

1. **Parity directive** (2026-07-24, load-bearing): identical behavior
   to Z3; every change states its parity argument; schedulers may only
   select from the closure.
2. **Source-fidelity over equivalent-engine + empirical check**
   (2026-07-26): port the mechanism, not a lookalike (07b, 12c, 27).
3. **Trace payloads pin only when the checker consumes them** (12d⇄19a).
4. **Determinism**: `randomize=false`; pick ladders deterministic.
5. **No assume/admit/external_body** anywhere in the trusted layer;
   report any unavoidable exception.
6. **Budget shape**: `withLayerHeartbeats`, never
   fraction-of-remaining.
7. **Verify lemma names and import scope before typing; probe
   `.induct` shapes before writing case lists; `command grep` on this
   box; check `uptime` before trusting timings.**
8. **omega/Var**: omega only sees literal `Nat`/`Int`-headed
   comparisons — Nat-binder helper lemmas + explicit `Nat.*` term
   lemmas for abbrev-typed facts (25.4 lesson, recorded in
   TypesOrder.lean docstring).

## 9. Doc debt

- ~~DESIGN-nlsat-quadratic §4b declared-divergences block stale~~ —
  corrected with this commit (nla-26 eliminated all three; pointer to
  the live divergence list added).
- DESIGN.md §2/L3 5-shape trace language vs DESIGN-nlsat-quadratic §2
  8-shape: reconcile when 12d pins payloads (the 8-shape is the live
  one; DESIGN.md kept as the original architecture record).
- After nla-27: refresh compareCore docstring (minimal branch no longer
  "declared unreachable") and the behavioral pin suites.
