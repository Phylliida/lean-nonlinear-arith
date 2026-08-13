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

