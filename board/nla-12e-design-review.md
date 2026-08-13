## nla-12e design review `done` (2026-08-13, post-12e; comprehensive divergence/regret/deferred audit)

Danielle-requested comprehensive audit of the 12e lane (commits
`f012646`, `956f3a6`): the B&B search port, the checker discharge, the
gate lift, and the int1 tests.

### Verified clean against source (all `git show z3-4.12.5:`)

- **Conflict-counter reset across B&B rounds**: z3's `search()` resets
  `m_conflicts = 0` at ENTRY (`nlsat_solver.cpp:1493`, alongside
  `m_bk = 0` / `m_xk = null_var`) — exactly our `search`'s
  `conflicts := 0` (Solver.lean:798). Per-round budgets are z3's own
  semantics; no divergence introduced (or fixed) by 12e.
- **Scan condition and order**: `m_is_int[x] && is_assigned(x) &&
  !is_int(value)` over internal order 0..n (`:1562-1564`) =
  `collectIntBounds` verbatim, including the defensive unassigned skip.
- **Tighten loop**: `int_lt` (strictly-below, current-bound read for
  cells) + one-step `gt(v, lo+1)` compares to ⌊v⌋ (`:1566-1575`) —
  same compare sequence, same fixed point, same refinement threading
  (nla-28). Termination argument identical (non-integer v, lo0 < v).
- **Emission shape**: `mk_linear(1·x − c)`, GT-then-LT, `is_even =
  false`, one 2-literal clause per var, `learned=false`
  (`mk_clause(…, false, nullptr)`, `:1583-1602`) ✓. Note the
  mk_ineq_atom normalization gap (boarded, 12c-fidelity/nla-16) is
  INERT here: `x − lo`'s leading monomial has coeff +1 — no flip
  either way.
- **Restart**: `init_search` unwinds assignments/levels, learned
  clauses persist (`:1580` + init_search body) = our `initSearch`;
  cell refinements/became-basic conversions persist at heap level in
  both.
- **`am::is_int` port** (`algebraic_numbers.cpp:246`): minimal-flag
  short-circuit = `m_not_rational`; refine-to-width-½; ⌊upper⌋
  candidate; became-basic on hit; and NO save/restore wrapper
  (unlike `is_rational` :285) — `RAlg.isInt` documents exactly this.
- **Dead parameters**: `peek_in_complement`'s `is_int` (only the
  `nullptr && randomize` branch reads it, `:687-704`) and the
  defensive `!is_int(vlo) → continue` (our `intLtC` returns `Int`) —
  documented non-divergences.
- **Checker-side soundness of decision 1**: the context integrality
  hyp is the USER's own assumption — using it can never be unsound;
  a trace branching a non-integral var simply never closes. The
  split's validity needs only `lo` (any integer splits), so garbage
  payloads degrade to valid-but-useless clauses.

### Fixed same-day

- **F-i (coverage): multi-var single-round emission was unpinned.**
  int1 branches one var per round; the collect-all + single-restart
  path (one scan emitting TWO branch clauses) had no driver. Added
  `goInt2` (`{x0² = 2, x1² = 3}` over two int vars): round 1 emits
  `.intBranch 0 (-2)` + `.intBranch 1 (-2)` in one scan. Bonus
  coverage in the walked snapshot: the final DAG refutes via the x0
  side alone, so the x1 branch bundles are discharged-but-unreferenced
  and the x1 eq input never enters the referenced-input contract —
  precheck's bundle-less-input filtering is pinned load-bearing. Walks
  end-to-end with both integrality hyps (multi-hyp
  `introToClauseHyp` + per-var matching).
- **F-ii (doc):** `introToClauseHyp` had been given walkRefutation's
  doc text; now describes the helper (incl. the trailing-binder
  behavior: anything after the clause hyp stays in the goal → the
  walk's final `assign` fails = sound rejection).

### Considered, not boarded (with reasons)

- **lt-side decode arm unreachable via `lo` corruption alone**: the
  two split polys share `lo` (x−lo, x−(lo+1)), so a payload corruption
  always trips the gt check first; the lt arm fires only on
  independently-corrupted clause literals (foreign-trace fixture
  surgery for a same-class `throwError`). The gt-side pin
  (`int1BundlesBadLo`) represents the class.
- **Temp-cell allocation per tighten iteration** (append-only store
  grows one cell per compare; z3 uses stack `scoped_mpq`): perf-only,
  bounded by the same loop count as z3; nla-16 measurement territory.
- **Integrality hyps must PRECEDE the clause hyp** (introToClauseHyp
  intros to the first ∀-binder; later hyps stay under the goal and the
  final assign fails loudly): the nla-14 frontend owns the emission
  order; documented in HANDOFF. Generalizing the walk to intro past
  hC is needless for our goal shapes.
- **z3's first-root choice** (int1: we branch −√2 before +√2): our
  picker's order; z3 may differ. Search-side, untrusted — folded into
  R-iii's differential batch (int1 + int2 + pd1/pd2/pd3/pd4/pd6 vs
  the `/tmp/z3-4.12.5` shell) at nla-16.
- **`isV0` now means `!isS1Gated`**: the name stays (rename churn
  rejected at the Slice-3 review); the docstring carries the meaning.

### Deferred inventory after 12e (all boarded)

G7 (rootGeneric deg ≥ 3, Tier B — the only remaining isV0 gate), G8/G9/
G10 (nla-16 measurement), R-iii differential batch (nla-16), the
mk_ineq_atom normalization (12c-fidelity/nla-16), the L1 hardening set
(nla-21/22/23/07b — none block M3/M6), nla-31 termination proofs,
nla-06/nla-10. Nothing found in this review is unboarded.
