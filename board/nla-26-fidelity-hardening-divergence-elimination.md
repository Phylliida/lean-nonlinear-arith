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

