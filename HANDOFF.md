# HANDOFF — 2026-08-07 (12d.6b⇄19a: F2 COMPLETE for the acceptance driver — design review 5 re-scoped step-fact collection; F3 DAG walk next, recipe below)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` (execution units; the nla-19a entry has
the F1–F5 and R1–R9 decisions, design reviews 3 (R1'/R2'), 4
(R-i–R-viii), and **5 (V-a–V-e, F-i–F-iv, the re-scope)**), then
`WRITEUP.md`. Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
has the session history. Build: Nix `lake` on PATH (not elan);
`lake build` green (7608 jobs).

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>`, never the working tree.**

## Where we are

The **12d.6b ⇄ 19a arc**: trace layer, trusted discharges, Q1 coverage
theorems, F0/F1/F3-engine (`Assemble.lean`), and now **F2 COMPLETE for
the acceptance driver** (`Nlsat/Refute.lean` + `RefuteTests.lean`).
Design review 5 (BOARD) ran the phantom-bug playbook — probe before
building — and found the HANDOFF's "step facts load-bearing for
bundles 6/7" prediction was FALSE (traced to a core-polarity
mis-transcription of the dump; `arithClause = proj ++ ¬core` is the
only valid reading). The real gaps were glue-level and are FIXED:

- `ring_nf at *` after the evalP simp-unfold (post-simp `ρ x ^ 1` /
  `↑(-1)` spellings are not linarith-normal even when pp-identical
  hand-written contexts close — open root-cause trap, recorded);
- lazy disequality trichotomy splits (`¬(t = 0)` facts are invisible
  to linarith; `lt_or_gt_of_ne` + `MVarId.cases`, one diseq at a time,
  glue retried per branch, de-dup by fvarId, fuel 8).

All five driver arith lemmas (bundles 6/7, final cores 1-3) are pinned
in `RefuteTests.lean` + a negative probe; the x0²+x1²<0 pins stay green.
**Step-fact collection (Coverage-theorem consumption) is re-sequenced
to a census-driven slice AFTER F3/F4** (BOARD review 5, F-iii): the
identified non-literal-local case is `rootGeneric`; the census slice
also owns F-iv (multi-factor ¬EQ collapse, even-parity variants in
`extractFact`).

Remaining in the arc: **F3 DAG walk → F4 acceptance → F5 housekeeping**
→ the census slice → 19b (pseudoDivision/factorSplit identities), 12e,
14, 15, 16.

## Next: F3 — the propositional DAG walk

Everything needed is already landed or pinned. Recipe (review 4,
R-iv/R-v/R-vi + the F2-groundwork block):

1. **Input:** the solver snapshot (`s.refutation` seam pre-restoreOrder,
   F2): `atoms : Array (Option Atom)`, `clauses : Array (List Literal)`,
   `traceBundles : Array (Option TraceBundle)` (parallel to clauses;
   `none` ⟺ input clause, V-iii), `finalRefutation`.
2. **Per learned cid in increasing order** (antecedent cids are always
   smaller — creation order): F-set = antecedent clauses (input from Γ
   hypotheses, learned from earlier fold steps) ∪ the bundle's arith
   clauses (F2 output — `nlsat_arith_valid` discharges each
   `clauseSatI (interp ρ atoms) (arithClause core proj)`); target =
   `bundle.lemma.toList` (assert byte-identical to `clauses[cid].lits`
   by `decide`, V1); skip `.decision` markers. Apply `upRefutes_sound`
   with the RUP check `by decide` (NEVER native_decide in the trusted
   layer; per-bundle-local kernel cost, R-v).
3. **Final bundle:** target `[]` ⇒ `False`. Theorem shape (R-vi):
   `∀ ρ, (∀ input clause C, clauseHolds ρ atoms C) → False`, bridged
   via `clauseSatI_interp` (per-literal decodability
   `∃ a, atoms[l.bvar]? = some (some a)` by `decide`, reject on
   failure). Hand-verified on the driver dump: ¬target units
   `⟨5,true⟩` against input clause 5 → conflict.
4. The walk is UNTRUSTED meta producing kernel-checked terms (same
   trust shape as Refute.lean, R-viii); RUP/UP engine + `upRefutes_sound`
   are the trusted core and already exist (`Assemble.lean`).

The driver's full refutation reproduced via `lean --run` (recipe in
BOARD's F2-groundwork block) is the working example; its bundles/cids
are small and fully enumerated in the BOARD dump analysis.

## After F3

- **F4 acceptance:** the 2-var driver end-to-end (search → trace →
  checked theorem from the snapshot); factorSplit-bearing trace
  x²+2x+1 (may pull the 19b identity forward, accepted risk); negative
  probes per R4' (corrupted mkNeg, corrupted sp — parse-level
  rejections via the E1 grammar tightenings); decode-success assertions
  on every step (R-ii); all 12c/12d pins re-green.
- **F5 (R8 + R1'):** split Check.lean into Semantics/Discharge; unify
  discharge hypotheses on full `MPoly.Canon`; normalize `↑0`-form
  hypotheses to `(0 : ℝ)`.
- **Census slice (new, from review 5):** grammar-coverage census —
  per grammar shape, is the arith-clause contradiction literal-local
  (closes from literal failures + glue) or not? Non-local cases get
  step-fact collection via the Coverage theorems (recipe from the old
  HANDOFF's bundle-6/7 sections, still valid as the mechanism design:
  `coverage_linearRoot`/`coverage_thomQuadratic` assembly, R-iii
  root-order injection, R-ii by-value reconstruction) + the F-iv
  `extractFact` extensions (multi-factor EQ collapse, even parity).
  `rootGeneric` definite-disc is the known member.
- **Then:** 19b (identities → M3; `ordering_139` standing target),
  12e (integer branching), 14 (the `nonlinear_arith` tactic,
  `withLayerHeartbeats`), 15 (tactus wiring, ½ session), 16 (parity
  harness).

## Traps / lessons (new this session — also in BOARD review 5)

- **Phantom-bug, third occurrence:** the HANDOFF's English transcription
  of the dump's arith clauses used the UN-negated core (invalid
  reading) and predicted spurious machinery (step-fact collection for
  bundles 6/7). Verify decodes against the raw dump + `arithClause`
  def BEFORE designing against them. Hand-countermodel check: with
  core un-negated, bundle 6's clause is falsifiable (x0=0, x1=−0.5).
- **linarith vs post-simp spellings (open root cause):** the evalP
  simp-unfold leaves `ρ x ^ 1` and `↑(-1)` forms that linarith fails on
  even though pp-identical hand-written contexts close. RULE: `ring_nf
  at *` after the simp-unfold, before any linarith/nlinarith glue.
- **Disequalities:** `¬(t = 0)` is invisible to linarith/nlinarith —
  trichotomy-split it (`lt_or_gt_of_ne`), lazily, de-dup by fvarId
  (branch contexts inherit the diseq; un-de-duped re-splits burn fuel
  on rejection paths).
- **`replaceMainGoal` throws on an empty goal list** ("No goals to be
  solved") — after closing a branch the list IS empty; use `setGoals`
  for explicit goal management.
- **`#guard_msgs (drop error)` takes the command's DOCSTRING as the
  expected message** — rejection probes must carry plain `/- -/`
  comments, never `/-- -/`.
- `List Literal` has no `ToMessageData` — repr-map in error messages.
- Meta-elaboration probes: `Elab.Term.elabType` of quotations inside
  `withContext` can leave level/type mvars and resolve context fvars to
  `sorryAx` if the name isn't in term scope — diffing exprs against
  hand-elaborated twins is fragile; prefer semantic probes (does the
  glue close?) over structural ones.

Standing (unchanged, see BOARD/memory for full lists): kernel-reduction
trap (literal-list polys at the checker seam; `Canon` meta-assembled;
`upRefutes … by decide` safe — Nat/Bool only); `(0 : ℝ)` numeral
discipline until F5; withContext for all meta ops touching context
fvars; `Exists.intro` motive explicit; `mkAppOptM` for zero-arg
constants; `command grep` on this box; check `uptime` before timings.
