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

