# HANDOFF — 2026-08-13 (19b COMPLETE — Slice 3 gate lift + pd1 walked;
# **M3 DECLARED**; next = 12e: G6 integer B&B, where the leftover
# intBranch gate lifts)

Read first: `DESIGN-endgame.md`, then `BOARD.md` — newest entries:
"nla-19b Slice 3 `done`" (gate lift + pd1 acceptance; the `/--`-above-
`#guard` parse trap), "nla-19b Slice 2 design review `done`" (**the
mk_ineq_atom normalization gap** — our mkIneqAtom doesn't
flip_sign_if_lm_neg ineq factors; search-side, boarded for
12c-fidelity/nla-16; the lane's lc lookup is negation-tolerant via
signFlipFactFor), "nla-19b Slice 2 `done`". Build system: Nix `lake` on
PATH (not elan); full build green (7612 jobs), WORKING TREE CLEAN,
everything committed.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

**19b Slice 3 landed → M3 DECLARED** (BOARD "nla-19b Slice 3 `done`",
milestone-ladder flipped). `isV0` drops `.pseudoDivision` (Trace.lean;
`.intBranch` stays gated → 12e); `nodeFSet` passes pd steps through
with no clause-level facts (projection-step treatment, review-5 F-i);
`buildFSet` already forwarded via `priorSteps` — no change needed.
pd1 snapshot regenerated post-lift into WalkTests and walked end-to-end
(solver learns `x0² < 0` — the path-(e) rebuilt literal — off
`pseudoDivision x1 (x1−x0²) 1 1 x0² 1 false`, then `leafNumeric` kills
it). Pins: gate guards (pd v0 / intBranch not), step-free
(glue-subsumption at walk level), corrupt-R (skip + glue closes),
grammar-bad lcSign=2 (precheck reject — the grammar gate is now a pd
bundle's first line, no longer masked by isV0). With o139 (G11
session), both 19b acceptance targets walked = M3 per DESIGN-endgame
§2.5.

Pre-session housekeeping committed separately (52ee0f8): the previous
session's BOARD.md → board/ split was uncommitted despite the old
HANDOFF's "clean tree" claim.

## Next: 12e (G6, integer branch-and-bound) — 1–2 sessions

Spec: BOARD "nla-12 `active`" + DESIGN-endgame §2.6. Verus VCs are ℤ,
nlsat is ℝ. Port z3's integer handling for the nlsat path:
branch-and-bound splits (`x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉` at non-integer witnesses)
as `intBranch` trace steps — checker-side each split is an
omega-trivial disjunction, so this is search-side work almost entirely.
Confirm against source where solver-6 does the splitting for the nra
path (nra_solver.cpp / nlsat's branch analogue) and port that exact
policy. L1 already owns div/mod semantics (RULES rows); L2 sees
polynomial atoms only — assert this invariant at the frontend boundary.
Close-out lifts the leftover `intBranch` gate (isV0 + nodeFSet, the
two sites Slice 3 touched) and flips the G6 row. Two Slice-3-review
items land here: **R-iv — `grammarOK`'s intBranch arm is currently
unconditionally `true`; when the gate lifts, add the decide-grade
structural condition (`v.den ≠ 1` — z3 branches only at NON-integer
witnesses) per the Slice-1 structural-grammar pattern** (witness
consistency stays discharge-side). Candidates for co-scheduling: the
mk_ineq_atom normalization gap (Slice-2 review finding) if
12c-fidelity lands here rather than at nla-16.

## Roadmap after 12e (unchanged)

nla-14 (the `nonlinear_arith` tactic, 2–3 sessions; owns F-y; largest
remaining piece) → nla-15 (tactus wiring, ½) → nla-16 (parity harness,
1–2 + findings; owns G8/G9/G10 **and the Slice-3-review R-iii: pd-driver
z3-binary differential probe** — pd1/pd2/pd3/pd4/pd6 through the
`/tmp/z3-4.12.5` shell, conflict counts + emitted payloads vs the
WalkTests/RefuteTests snapshots) = M6. Total-to-M6 ~5–9 sessions.
Tier B (G7 rootGeneric deg ≥ 3, S1 lane) deferred unless 16's harness
shows the corpus needs it. Q7: re-offer 11a (resultants) as the
interleave lane — 19b has landed, so the offer is live.

## Session mechanics + traps (cumulative; F3/F4 section of commit
d9d5df1 still accurate for dump/refresh recipes)

- **A doc comment (`/-- -/`) directly above `#guard` fails parsing**
  with "unexpected token '#guard'; expected 'lemma'" — docstrings
  attach only to declarations; `#guard` isn't in the post-docstring
  command first-set. Use `/- -/` for guard pins.
- `scratch_dump.lean` needs `lake env lean --run` (it defines `main`;
  bare `lake env lean` elaborates silently and prints nothing).
- The previous session's working tree was NOT clean despite the old
  HANDOFF's claim (the board split) — verify `git status` at session
  start, not just the HANDOFF.
- **'_tmp✝' kernel free-variable errors are elaboration
  error-recovery artifacts** — an `unknown identifier` upstream (a
  missing def in a scratch) makes the elaborator synthesize junk that
  the kernel then reports as free variables. Grep for the REAL error
  first; do NOT chase the mvar table (an hour lost this session).
- `closeAlgRefl`/`closeNumerically`/`closeSigProd` now wrap their
  sandbox in `withoutModifyingState` (rolls the mvar table back over
  the ring/norm_num attempt — defense-in-depth for the Slice-1 hole
  class; success path unchanged, term extracted before rollback).
- Inductive PARAMETERS are implicit in constructors:
  `mkAppM ``SignRel.nil #[ρ]` is "too many explicit arguments" — use
  `mkAppOptM … #[some ρ]` (same for `List.nil`).
- `let mut` CANNOT be assigned inside a `withContext` closure —
  thread an explicit state record (the lane's `PdState`).
- A do-block `try` arm must end in a VALUE, not a bare assignment
  (`S := …` then `pure ()`).
- Structure-update syntax across a line break misparsed inside a
  nested `try` ("unexpected identifier; expected '}'" at the line
  end) — keep `{ S with … }` on one line.
- Inline `nlsat_arith_valid_steps #[…]` payloads with `(-1)` Int
  literals (or empty monomials) leave mvars at `evalExpr` — named
  `Array TraceStep` defs with ascriptions (the HANDOFF trap extends
  from `(-1), []` monomials to bare `(-1)` lcSign literals).
- Multi-example scratch files: Lean sorts diagnostics by position —
  logInfo instrumentation lines do NOT interleave with errors in
  temporal order; read by position.
- The earlier traps stand (block-buffered `--run` output; `lake
  build <module>` BEFORE `lake env lean scratch.lean`; swallowed
  try/catch instrumentation recipe; `Eq.mp` forward / `Eq.mpr`
  BACKWARD; `hasMVar` on produced terms; `(0:ℝ)` annotation;
  `Or.getAppFnArgs` = `#[A, B]`).

Commits this session: `52ee0f8` (board split housekeeping), `09a75b0`
(gate lift), `2b6116e` (pd1 walk + pins) + the close-out docs commit.
Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
updated (2026-08-13 Slice-3/M3 entry; NEXT SESSION ORDER line current).
