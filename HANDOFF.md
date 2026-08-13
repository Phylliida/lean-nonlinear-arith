# HANDOFF — 2026-08-13 (12e DONE in one session — integer B&B ported
# end-to-end, G6 closed, **isV0 := !isS1Gated** (the last shape gate
# lifted); next = nla-14: the `nonlinear_arith` tactic — the largest
# remaining piece)

Read first: `DESIGN-endgame.md`, then `BOARD.md` — newest entries:
"nla-12e `done`" (the B&B port + decisions 1–2 + the int1 two-round
walk), "nla-12e plan `done`", "nla-19b Slice 3 design review `done`"
(**R-iii: pd drivers are source-reading-anchored only — z3-binary
differential probe boarded for nla-16; int1 folds into that batch**;
the mk_ineq_atom normalization gap — our mkIneqAtom doesn't
flip_sign_if_lm_neg ineq factors; search-side, 12c-fidelity/nla-16
lane). Build system: Nix `lake` on PATH (not elan); full build green
(7612 jobs), WORKING TREE CLEAN, everything committed.

**Source-of-truth rule: all ports cite `git show z3-4.12.5:<path>`
(repo `verus-cad/z3`), never the working tree.** Standing directive
(Danielle): cover ALL cases no matter how rare. z3-4.12.5 build for
differential probes: worktree `/tmp/z3-4.12.5` (`make -j shell`).

## State of the arc

**M3 declared** (19b Slice 3, earlier today) and **12e landed the same
day**: z3's integer branch-and-bound (`nlsat_solver.cpp:1554-1606`)
ported search-side (collectIntBounds scan + intLt/tighten +
initSearch restart + emitIntBranch) with the `intBranch` payload as
`(x, lo : Int)` — exactly what z3 puts in the emitted clause (decision
2; R-iv dissolved by construction). Checker side: the split is
discharged from the CONTEXT's integrality hypothesis **`∃ n : ℤ,
ρ x = ↑n`** (decision 1 — this is the convention nla-14's frontend
will emit per Int-typed var; the walk's `introToClauseHyp` intros past
such hyps). int1 (`{x0² = 2}` over one int var, TWO B&B rounds) walked
end-to-end; probes pin missing/wrong-var integrality rejection and
payload-mismatch rejection. `isV0` is now just the S1 fragment gate.

## Next: nla-14 — the `nonlinear_arith` front-end tactic (2–3 sessions)

Spec: BOARD "nla-14" + DESIGN-endgame §2.7. The pieces:
- **Layering:** L1 `nla_saturate` first (fast path, most goals), on
  failure L2/L3 search+check. Budgets per the BUDGET-SHAPE lesson:
  `withLayerHeartbeats` (fresh user budget per layer, Z3-per-module
  analogue) — never fraction-of-remaining.
- **Int → Real atom mapping** + 12e's integrality-hyp emission
  (`∃ n : ℤ, ρ x = ↑n` per Int-typed var — the convention decision 1
  established; the checker consumes it in `intBranchSplitProduce`).
  ℤ ⊆ ℝ relaxation direction is sound for proving (goal proven over ℝ
  with ℤ atoms specializes); div/mod never reach L2 (L1-owned) —
  assert this invariant at the frontend boundary.
- **Hypothesis selection:** Verus query shape — context-free, only
  stated `requires` (matches the spinoff query Z3 sees; no
  ambient-context mining beyond what L1 already does).
- Owns F-y.

## Roadmap after nla-14 (unchanged)

nla-15 (tactus wiring, ½ session; toolchains aligned, a `require`
line + closer-string emission) → nla-16 (parity harness, 1–2 +
findings; owns G8/G9/G10 + **R-iii: pd-driver + int1 z3-binary
differential probe** via `/tmp/z3-4.12.5`) = M6. Total-to-M6 ~4–7
sessions. Tier B (G7 rootGeneric deg ≥ 3, S1 lane) deferred unless
16's harness shows the corpus needs it. Q7: re-offer 11a (resultants)
as the interleave lane.

## Session mechanics + traps (cumulative; F3/F4 section of commit
d9d5df1 still accurate for dump/refresh recipes)

- **A doc comment (`/-- -/`) directly above `#guard` fails parsing**
  with "unexpected token '#guard'; expected 'lemma'" — docstrings
  attach only to declarations; use `/- -/` for guard pins.
- `scratch_dump.lean` needs `lake env lean --run` (it defines `main`;
  bare `lake env lean` elaborates silently and prints nothing).
- Verify `git status` at session start (the 19b-Slice-2 session's
  board split was uncommitted despite its HANDOFF's "clean tree").
- **`break` works in do-notation `while` loops** (used in
  searchCheck's B&B loop); `let mut` still can't be assigned inside a
  `withContext` closure (thread a state record).
- **'_tmp✝' kernel free-variable errors are elaboration
  error-recovery artifacts** — grep for the REAL error first (an
  `unknown identifier` upstream); do NOT chase the mvar table.
- `closeAlgRefl`/`closeNumerically`/`closeSigProd` wrap their sandbox
  in `withoutModifyingState` + `hasMVar` checks on produced terms
  (the Slice-1 hole class).
- Inductive PARAMETERS are implicit in constructors (`mkAppOptM …
  #[some ρ]`).
- A do-block `try` arm must end in a VALUE, not a bare assignment.
- Structure-update syntax across a line break misparses inside a
  nested `try` — keep `{ S with … }` on one line.
- Inline `nlsat_arith_valid_steps #[…]` payloads with `(-1)` Int
  literals (or empty monomials) leave mvars at `evalExpr` — named
  `Array TraceStep` defs with ascriptions.
- Multi-example scratch files: diagnostics sort by position — logInfo
  lines don't interleave with errors temporally.
- The earlier traps stand (block-buffered `--run` output; `lake
  build <module>` BEFORE `lake env lean scratch.lean`; swallowed
  try/catch instrumentation recipe; `Eq.mp` forward / `Eq.mpr`
  BACKWARD; `(0:ℝ)` annotation; `Or.getAppFnArgs` = `#[A, B]`;
  `Int.lt_or_ge` doesn't exist — use the generic `lt_or_ge`).

Commits this session: `52ee0f8` (board split housekeeping), `09a75b0`
+ `2b6116e` (19b Slice 3 + M3), `33b2f18` (Slice-3 close-out),
`f7a0bfc` (poem), `371babf` (Slice-3 design review), `f012646` (12e)
+ the close-out docs commit. Memory file
`verus-cad/memory/project_tactus_nonlinear_port.md` updated (12e
entry; NEXT SESSION ORDER line current).
