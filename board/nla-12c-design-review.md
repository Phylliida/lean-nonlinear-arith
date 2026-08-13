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

