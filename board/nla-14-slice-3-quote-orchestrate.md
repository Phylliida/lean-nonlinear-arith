## nla-14 Slice 3 `done` (2026-08-14) — quote + orchestrate

Pre-implementation planning sweep, interface inventory verified against
the tree at `fd87598` (build green 7614, tree clean). Sources:
`board/nla-14-plan.md` (Slice-3 scope), `board/nla-14-slice-2-…` (the
hand-off traps), HANDOFF.md. Slice 3 = the solver run in TacticM, the
five quoters, the proxy-def patch, the post-run Cs rebuild, SAT-exit
model display (decision 4), and the pins. Slice 4 (the
`nonlinear_arith` elab + layering + acceptance) stays separate.

### The central restructure (drives everything else)

Slice 2's `toRefutationGoal` (Tactic/NonlinearArith.lean:1178) fixes the
refutation goal from `st.atoms` BEFORE any solver run and drops
`ReifyState`/`BridgeCtx` at return. That flow cannot be walked:
`Walk.precheck` (Walk.lean:124) demands `snap.atoms == goalAtoms`
EXACTLY, and the run-time snapshot differs from `st.atoms` three ways:

1. **Internal var order.** `check` (Solver.lean:1365) runs
   `heuristicReorder` (:1270 — arith vars only; bvar indices and clause
   ids untouched) and captures `s.refutation` in INTERNAL order
   (:1376-1379) before `restoreOrder`. The snapshot's ineq-atom polys
   are `renameVars`'d (identity on sq/int1/int2-class inputs,
   non-identity on o139-class).
2. **Proxy slots.** The solver table has `none` at proxy bvars; the
   goal table needs `.bool d`. Patch post-run, keyed by bvar —
   reorder-stable, since reorder never touches bvars and
   `renameAtoms` leaves `.bool` alone (Solver.lean:1218-1229).
3. **Solver-appended atoms.** `emitIntBranch` (:1335) appends atoms
   during `check`; the snapshot table can be strictly larger than
   `st.atoms`. Fine for precheck (goal atoms = snapshot atoms, both
   taken from the patched snapshot), but bridges must be built against
   the PATCHED table, not `st.atoms`.

So Slice 3 inverts the order: **reify → register into the solver →
run → patch → THEN build the goal + bridges from the patched snapshot
→ walk.** `nla_frontend` keeps its current dev behavior for the
existing hand-walked pins (it never runs the solver, so its goal stays
`st.atoms`-based); the orchestration path is new code that reuses the
phase-1 reify/clausify machinery but defers goal assembly.

### The permutation question — RESOLVED: A (Danielle, 2026-08-14, by the standing principles: A is z3's own code path byte-for-byte (4), reads the permutation directly instead of a matcher that cannot cover solver-appended intBranch atoms (1, 2), and does it now (3))

The walk's goal quantifies `ρ : Nat → ℝ` over INTERNAL var numbering
(snapshot order). The bridges (`mkAlign` etc.) relate user terms to
`evalP` of the snapshot's polys under `ρ*`, so `ρ*` must be defined in
internal numbering — we need the internal→external var map.

- **A (recommended): inline the `check` shell in the tactic.** All
  pieces are public: `initSearch` :793, `canReorder` :1132,
  `heuristicReorder` :1270, `sortWatchedClauses` :1290, `searchCheck`
  :1351, `restoreOrder` :1282. Run them in sequence in SolverM, read
  `s.perm` AFTER the snapshot capture and BEFORE `restoreOrder`, then
  restore (so the SAT model comes out in external order for display).
  Same code path as `check` — byte-identical fidelity (constraint 2),
  permutation read off directly.
- B: poly-match snapshot atoms back against `st.atoms` (renameVars is
  injective, atoms are hash-consed unique). No solver-shell
  duplication, but a fiddly matcher that must also handle
  solver-appended intBranch atoms (not matchable — they're new).
- C: skip reorder in the tactic path. REJECTED — performance-parity
  divergence from z3 (plan decision principle 4), and WalkTests pins
  were generated WITH reorder so snapshot shapes would shift.

A also hands us the cid-0 question for free: with the shell inlined we
see exactly what `init`/`searchCheck` did, including whether the true
clause is ever cited.

### Work items, in order

1. **Expose phase 1.** Refactor `toRefutationGoal` so reify+Tseitin
   (phase1, :1157) returns `ReifyState` (+ whatever bridge inputs
   Slice 2 computes per clause) instead of dropping them. `nla_frontend`
   keeps its signature; the new orchestrator calls the same phase 1.
2. **The five quoters.** New module `Nlsat/Quote.lean` (MetaM
   Expr-builders; DumpPP/scratch_dump.lean:12-91 is the grammar
   reference — it covers all 9 TraceStep arms incl. `pseudoDivision`'s
   7 fields and `intBranch (x, lo)`). MOVE the frontend's
   `ineqKindToExpr`/`boolDefToExpr`/`atomToExpr`/`optAtomToExpr`/
   `atomsToExpr` there (plan doc: "MOVE or share") next to
   `Refute.litToExpr`/:53 and `Refute.thomStepToExpr`/:67 — reuse
   `thomStepToExpr` for that arm rather than re-quoting. New:
   - `quoteClause` — `Clause.mk` over `Array Literal` (List.toArray
     idiom per `atomsToExpr` :76-79) + `learned`/`deleted` bools.
   - `quoteStep` — all nine arms; MPoly/Int/Nat/Bool via core `toExpr`
     (MPoly is `List (Int × List (Nat × Nat))`, no custom quoter
     needed — the Refute.lean idiom). No `Rat` anywhere in TraceStep.
   - `quoteBundle` / `quoteOptBundle` — `TraceBundle.mk` :204-207.
   - `quoteSnapshot` — nested `Prod.mk` over the four arrays
     (`SnapshotTy` = Walk.lean:64-67, exactly the `refutation` payload).
3. **Solver run in TacticM.** `unsafe` (evalExpr transitively — the
   walk is `unsafe`, Walk.lean:343). `(prog.run Solver.empty)` NOT
   `Solver.run'` (drops the state, Solver.lean:170-174) and NOT
   `default` (field defaults). Registration replay from `ReifyState`:
   `Solver.init` (creates bvar 0 + input clause cid 0 — the +1 cid
   shift, see traps) → per slot `mkVar (isInt := …)` (ℝ/ℤ/ℕ per
   `varTy`) → per proxy slot `mkBoolVar` → per clause
   `mkIneqLiteral`/`mkClause #[…] false`. **Assert** each
   `mkIneqAtom`-returned bvar == the expected slot (hash-consing
   collapse guard, Solver.lean:215) — fail loud, don't assume.
   Production explain: `Solver.resolve Explain.explain`
   (Explain.lean:866).
4. **Patch + rebuild.** Into the extracted snapshot: write `.bool d`
   at each proxy bvar (defs from `ReifyState.proxies`, bvar-keyed —
   must preserve emission order so the patched table still satisfies
   `boolDefsOrdered` for `BridgeCtx.hordPrf`). Rebuild `Cs` to the
   REFERENCED bundle-less input clauses only (precheck's contract,
   Walk.lean:150-166 — collect `.resolution (.clause cid)` antecedents
   with `none` bundles, ascending cid, drop everything else incl. the
   never-cited cid-0 true clause). Bridges are per-clause, so
   selection is by construction.
5. **Bridges against the patched table.** Rebuild `BridgeCtx` with
   `atomsE` = patched snapshot table (internal order), `ρ*` =
   `rhoStarExpr` composed with the captured `perm` (slot i := user
   value of external var `perm[i]`), integrality hyps at the INTERNAL
   indices (still `∃ n : ℤ, ρ i = ↑n`, still BEFORE the clause hyp).
   Reuse ALL of Slice 2's bridge machinery unchanged — it is
   parameterized on `BridgeCtx`; the WF-defeq traps are already paid
   (`boolDefHolds_*` equation lemmas + `boolDefHolds_evalLitHolds` :
   715 boundary, never `simp [boolDefHolds]`).
6. **Orchestrate.** Assemble `refTy` (Slice 2's :1249-1267 shape) from
   the patched atoms + pruned Cs; assign the original goal via the
   dispatch chain; close the refutation goal by
   `Walk.walkRefutation mvar snapE` directly (skip the `nlsat_refute`
   elab — it re-elaborates a term; we already hold Exprs). Keep the
   one-applied-`precheck` native-eval discipline (Walk.lean:23-29).
7. **SAT exit — model display (decision 4).** Post-`restoreOrder`,
   `s.assignment : Array (Var × CellId)` is external-order; per var,
   `s.store[cid] : RAlg` (CellStore.lean:36): `.rat q` → print q;
   `.root p a b m` → `RAlg.refineUntilPrec` (:166, pure — do NOT use
   the stateful `CellStore.refineUntilPrecC`, the search is over) then
   print `root of p ∈ [a,b]` via `ToString Mpbq` (Mpbq.lean:375).
   Map var → user expr via `ReifyState.varKeys`. Proxy vars carry no
   assignment — skipped automatically (only print `s.assignment`, not
   `s.bvalues`). Note the ℤ-relaxation caveat in the message for
   integer goals (an ℝ-model need not specialize). Clean `throwError`
   with the model — never a wrong close.
8. **undef/fragment exit.** Bounded fallthrough error naming the gate
   (plan doc:95).

### Pins (NonlinearArithTests + new driver tests)

- sq/xl ℝ and int1/int2 ℤ drivers in USER syntax, search → trace →
  checked theorem, NO hand-written snapshot (the WalkTests pasted-defs
  pattern replaced end-to-end).
- D-1: disjunctive driver with a proxy inside a LEARNED clause (the
  patched-table bridge must serve a clause the frontend never emitted).
- Foreign-`.arith`-with-proxy → sound REJECTION (extractFacts has no
  `.bool` lane; expect the glue failure, pin the error).
- The Slice-2-deferred div/mod error-surface pin (`#guard_msgs`).
- Genuine-SAT goal → clean error WITH model display (decision 4).
- Reorder actually exercised: one driver whose degrees/occurrences
  force a non-identity `heuristicReorder` (o139-class), proving the
  perm/ρ* path. If the census drivers all reorder to identity, build
  one by hand.
- cid-0 probe: confirm no trace in the driver set references the
  true-bvar clause; if one ever does, precheck will demand
  `[⟨0,false⟩]` with a decodable atom at slot 0 (`none` poisons) —
  pin current behavior, don't engineer for it.

### Traps carried forward (inventory-confirmed)

- cid shift: `Solver.init` makes cid 0 the true-bvar unit; every
  frontend clause is +1 in the solver. Account when mapping referenced
  cids back to `defClauses ++ roots`.
- `unsafe` is transitive: orchestrator, and any test calling it, are
  `unsafe`.
- Bare-const evalExpr mis-eval: keep native checks inside the single
  applied `precheck` (Walk.lean:23-29).
- `boolDefsOrdered` decide proof must be rebuilt for the PATCHED table
  (new `hordPrf`), not reused from `st.atoms`.
- `.bool` never appears in solver-produced atoms (DumpPP's ppAtom
  lacks the arm BECAUSE the table never carries it) — the patch adds
  them; solver-appended atoms are always arith, always decodable.
- mkAppM/mkAppOptM implicit-pinning, `→`-vs-`↔` precedence, sandbox
  setGoals, `Membership.mem` arg order — all live traps from Slice 2,
  same file.

### Estimate + roadmap (unchanged)

Slice 3 ≈ 1–1.5 sessions (meta-heavy, no new trusted components — the
quoters and orchestration are untrusted MetaM; kernel re-checks
everything via walkRefutation). Then Slice 4 (the `nonlinear_arith`
elab, L1/L2 layering with `withLayerHeartbeats`, acceptance + design
review) closes nla-14 → nla-15 (tactus wiring, ½) → nla-16 (parity
harness; owns G8/G9/G10 + the R-iii probes) = M6.

---

## Close-out (2026-08-14, same day) — LANDED, build green 7615

Commits: `15fa48d` (this plan), `24ecfb6` (core), `a5ed72c` (pins).

**Landed as planned, decision A verbatim:** `Solver.checkCapturing`
(the `check` body with the perm read off between snapshot capture and
`restoreOrder`; `check = (·.1) <$> checkCapturing`, one code path, no
drift). `Nlsat/Quote.lean`: the moved atom/BoolDef quoters + the full
grammar (all 9 TraceStep arms, Clause/TraceBundle/snapshot; MPoly via
core `toExpr`, arrays via the `List.toArray` idiom).
`Tactic/NonlinearArith.lean`: `prelude` (True-short-circuit +
byContradiction + phase1 returning `ReifyState`), `assembleRefutation`
(bridge/dispatch/intWits/refTy parameterized on table + perm + clause
selection — Slice-2's `toRefutationGoal` is the identity-perm all-
clauses special case, pins unmodified), `orchestrate` = reify →
register → run → patch (bvar-keyed `.bool` defs into the snapshot
table) → referenced-inputs Cs rebuild (solver-sorted literal lists,
cid−1 frontend indexing) → bridges against the patched internal table
→ `walkRefutation`. SAT exit: per-var model display off the
post-restore assignment (`RAlg.refineUntilPrec 10`, proxy vars absent
by construction, ℤ-relaxation caveat when integer vars exist). undef:
bounded-exit error.

**Pins (NonlinearArithTests, `Tests.Orchestrate`):** sq/disj/proxy/
int1/int2/o139 in user syntax via `nla_solve` (NO hand-written
snapshots — the WalkTests data pipeline replaced end-to-end; o139 at
800k heartbeats, Slice 4 owns the budgeting); reorder driver `x < y*y
∧ y*y < x − 1` + the solver-seam `perm == #[1,0]` guard; D-1 guard
(learned clauses [5,6] carry the proxy bvar, final bundle resolves
them); foreign-`.arith`-with-proxy sound rejection (RUP-invariant
poisoning of a `.clause` antecedent into an `.arith` marker — precheck
passes, the arith discharge rejects; EXACT error message pinned);
SAT model display (exact message: `x := 1/2`); div/mod error surface;
undef via `maxConflicts := 0` (needs a BACKJUMPING input — sq and the
lt-cycle refute at stage 0 without one; the proxy driver trips it).

**Catches worth the books:**
- **Kernel caught a REAL Slice-2 bridge bug**: the `.le/.ge` arms at
  negative polarity (disproving an `a ≤ b`/`a ≥ b` goal — first
  exercised by o139's conclusion) assembled `¬(a≤b) ↔ ¬¬litHolds` —
  one `not_congr` too many. Now `not_congr (symm castLink) ∙ not_le ∙
  tailChain`. No Slice-2 pin had a ≤/≥ GOAL; the walk's kernel
  re-check of the full bridge chain did its job.
- Registration must `mkVar` BEFORE atoms/clauses (forgotten on the
  first pass: every pin reported SAT with an empty model — watches
  silently no-op'd on the empty `watches` array). Alignment assertions
  now cover isInt/atoms/clauses sizes + per-slot content.
- `mkAlign`'s sandbox needed `try push_cast`/`try ring`: simp fully
  closes LINEAR alignments (`evalP ρ* [(-1,[(1,1)])] = 0 - da`), and
  a trailing step on zero goals failed the sandbox (o139's `0 < da`).
- `Solver.run'` drops the state — use `(prog.run Solver.empty)`;
  `Solver.init` creates bvar 0 + cid 0 (the +1 shift);
  `st.roots`/`st.defClauses` lack Inhabited (`[i]?` + loud error);
  TraceStep lacks BEq/Inhabited (match, don't `==`/`[i]!`); doc
  comment above `#guard`/`set_option…in` still fails parsing;
  `return f a\n b` doesn't absorb multi-line applications (parens).

**Next: Slice 4** — the `nonlinear_arith` elab, L1/L2 layering
(`withLayerHeartbeats` sandboxed saturateCore, roll back to the
original goal on L1 failure), acceptance + negative probes, stats
variant, design review.
