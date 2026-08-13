## nla-12e `done` (2026-08-13) — integer branch-and-bound; G6 closed; the last shape gate lifted

Spec: `nla-12e-plan.md` (decisions 1–2 Danielle-resolved same day).
Landed in ONE session (estimate was 1–2). Commit `f012646`.

**Slice 1 (search side).** `searchCheck` is now z3's `search_check`
(`nlsat_solver.cpp:1554-1606`): post-SAT scan for is_int vars with
non-integer values (`collectIntBounds` — `intLt` + the one-step
tighten loop of algebraic-vs-rational compares, refinement threaded
through the store), collect-all, one `initSearch` (learned clauses
persist), per-var `emitIntBranch` (the 2-literal split clause,
`learned = false` — z3's `mk_clause(…, false, nullptr)` — with the
`intBranch` step flushed into the bundle). `RAlg.isInt` ports
`am::is_int` (`algebraic_numbers.cpp:246`: minimal-flag short-circuit,
refine-to-width-½, ⌊upper⌋ candidate, became-basic on hit; no
save/restore — faithful to the source's lack of one).
**Payload change (decision 2):** `(x, lo : Int)` — exactly what z3
puts in the clause; the algebraic (possibly irrational) sample is
never carried, and **R-iv dissolves by construction** (any integer
`lo` is a sound split; `grammarOK` unconditional by design).
**Verified non-divergences:** `peek_in_complement`'s `is_int`
parameter is DEAD under `randomize=false`
(`nlsat_interval_set.cpp:687-704` — no `pickInComplement` change);
z3's defensive `!is_int(vlo) → continue` is vacuous (`intLtC` returns
`Int`).

**Slice 2 (checker side).** Trusted: `Check.intBranch_split` (the
evalP split from CONTEXT integrality — decision 1) +
`notHolds_{gt,lt}_single_of_{nonpos,nonneg}` (Discharge.lean). Meta:
`Refute.findIntegralityHyp` (syntactic lctx scan for `∃ n : ℤ,
ρ x = ↑n`) + `intBranchSplitProduce` (by-value clause↔payload decode;
`clauseSatI` via the `clauseSatI_interp` bridge — the input-fact
idiom mirrored). `Walk.buildFSet` intBranch arm; `nodeFSet` arm
(contributes the bundle's lemma — RUP-trivial by construction; the
semantic gate is the decode + discharge). The input contract already
excluded bundle-carrying clauses — verified, NO change needed.
`introToClauseHyp`: integrality hyps may precede the clause hyp.
**Gate lift:** `isV0 := !isS1Gated` — every step shape now has a
checker lane; only the S1 fragment gate remains (Tier B). The
`nodeFSet` "non-v0 step" throw is deleted — no non-v0 shapes exist.

**Slice 3 (tests).** `int1` (`{x0² = 2}` over one int var): the solver
takes TWO B&B rounds (lo = −2 near −√2, then lo = 1 near +√2) and the
snapshot walks end-to-end with the context integrality hyp. Probes:
missing integrality → sound reject (goal genuinely unprovable —
`ρ 0 = √2` satisfies the input); wrong-variable integrality → reject
(per-var matching load-bearing); payload-mismatch `lo = 5` → by-value
decode reject. Gate guards flipped.

**Differential note for R-iii (nla-16):** the two-round trace
(−√2 first, then +√2) is OUR witness order; z3's first-root choice
may differ (search-side, untrusted) — fold int1 into the pd-driver
differential probe batch.

**Roadmap:** nla-14 (the `nonlinear_arith` tactic — owns the
integrality-hyp convention decision 1 established: `∃ n : ℤ, ρ x = ↑n`
per Int-typed var) → nla-15 → nla-16 = M6.
