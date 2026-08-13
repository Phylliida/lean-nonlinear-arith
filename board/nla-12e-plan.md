## nla-12e plan `boarded` (2026-08-13, pre-implementation planning sweep — G6 integer branch-and-bound)

Scope (HANDOFF + DESIGN-endgame §2.6 + Slice-3-review R-iv): port
z3-4.12.5's integer branch-and-bound for the nlsat path — search-side
emission of `intBranch` steps, checker-side discharge, the R-iv grammar
question, and the leftover gate lift (isV0 + nodeFSet). Acceptance:
an integer driver through search → trace → checked theorem end-to-end;
G6 row flips done. Effort estimate: 1–2 sessions, search-side-heavy.

**Source anchors (all `git show z3-4.12.5:`):**
`nlsat_solver.cpp:1554-1606` `search_check` — the B&B loop: `search()`
returns l_true → scan `x = 0..num_vars` for `m_is_int[x] &&
m_assignment.is_assigned(x) && !m_am.is_int(value(x))` → `int_lt(v,
vlo)` (integer STRICTLY below; for cells read off the CURRENT dyadic
bound, possibly loose), defensive `!is_int(vlo) → continue`, then the
tighten loop `do { lo++ } while (v > lo); lo--` (algebraic-vs-rational
compares, REFINES the cell — nla-28 statefulness) ending at
`lo = ⌊v⌋` → collect ALL offending vars → one `init_search()`
(learned clauses persist; assignments unwind) → per var a 2-literal
clause `{¬(x−lo > 0), ¬(x−(lo+1) < 0)}` (`mk_linear`, `is_even =
false`, `mk_clause(..., false, nullptr)` — input-flagged, no
justification) → re-enter `search()`. `algebraic_numbers.cpp`
`am::is_int`, `am::int_lt` (4.12.5: PURE, no refine — nla-32 anchor).
`nra_solver.cpp:507-509/:518-519/:524-526`: lp int vars become nlsat
int vars (`mk_var(is_int(v))`) — the Verus path DOES produce is_int
vars; our drivers so far all `mkVar false`.

**Recon findings (this session):**
- `Solver.isInt : Array Bool` + `mkVar(isInt)` already mirror
  `m_is_int`/`mk_var` (Solver.lean:111/:197); `searchCheck`
  (Solver.lean:1282-1287) is the declared 12e seam with the boundary
  comment. `initSearch` (Solver.lean:783) already mirrors
  `init_search`. `selectWitness` (Solver.lean:772) is the witness
  entry point.
- **`peek_in_complement`'s `is_int` parameter is DEAD under our
  configuration** (`nlsat_interval_set.cpp:687-704`): the only
  `is_int` read is the `s == nullptr && randomize` branch
  (`den = 1`); with `randomize=false` (our pinned config) the nullptr
  case returns 0 either way, and the witness ladder proper is
  is_int-blind. Our `pickInComplement` needs NO change — document as
  verified non-divergence, no parameter to port.
- `RAlg.intLt : RAlg → Int` (RAlg.lean:188) already ports 4.12.5
  `am::int_lt` (⌊v⌋−1 for rationals, ⌊lower⌋ off the current dyadic
  bound for cells — pure, no refine). The tighten loop needs
  algebraic-vs-rational compare with refinement threading (CellM —
  the assignment stores `CellId`s, Solver.lean:779).
- `am.is_int` port: `.rat q → q.den == 1`; `.root → false` (post-nla-27
  eager rational discovery + the `minimal` flag, a `.root` value is
  irrational, and an irrational is never an integer).
- **z3's `!is_int(vlo) → continue` branch is vacuous in our port**:
  `RAlg.intLt` returns `Int` (always "is_int"). Document.

**Trace/walk design (the consumption side):**
- Emission reuses the existing machinery: per branch var,
  `noteStep (.intBranch …)` → `mkClause lits false` → `flushTrace cid
  lits` (Solver.lean:365/:378/:384) — the branch clause is
  input-FLAGGED (learned=false, z3-faithful) but carries a SOME bundle
  whose lemma is the split clause itself.
- Walk: `precheck`'s per-cid loop keys on bundle PRESENCE, not the
  learned flag, so branch clauses flow through the learned path
  naturally. **The input-clause contract must exclude bundle-carrying
  clauses** (branch clauses are not in the goal's `Cs`) — one-line
  guard change at Walk.lean:139-150 (count only bundle-less clauses as
  inputs).
- `nodeFSet`'s intBranch arm (currently `throw "non-v0 step"`):
  contributes the split clause value (the bundle's lemma) to F — RUP
  then derives the lemma trivially. `buildFSet`'s arm: discharge
  `clauseSatI` of the split clause — **omega-trivial given integrality
  of x**: `n ≤ lo ∨ n ≥ lo+1` for `n : ℤ`, any integer `lo`. The
  discharge does NOT consume the sample value at all — only `lo`.

**Decision points for pre-implementation design review (Danielle):**
1. **Integrality provenance.** The split clause `{x≤lo, x≥lo+1}` is
   valid only under `ρ x ∈ ℤ`; the checker must obtain that fact
   soundly. (a) PROPOSED: the `buildFSet` discharge looks the
   integrality hypothesis up in the local CONTEXT (`∃ n : ℤ, ρ x = n`,
   the nla-14 frontend emits these for Int-typed vars; test goals
   state them explicitly) — absent → sound rejection. Zero snapshot
   churn; the trust boundary is exactly "the context proves
   integrality", and a foreign trace branching a non-int var can never
   close. (b) Alternative: extend `SnapshotTy` with an `isInt :
   Array Bool` table + goal shape gains per-int-var hyps — z3's
   `m_is_int` made manifest, but churns every pinned snapshot
   (o139/pd1/xl/rg/…) for a flag the discharge would re-check against
   the context anyway.
   **RESOLVED (Danielle, 2026-08-13): option (a).** Rationale
   accepted: z3's `m_is_int` is SEARCH-side state (our `Solver.isInt`
   already mirrors it there); z3's branch clause carries a nullptr
   justification — no var-table data crosses into anything a checker
   could consume. A snapshot table would be a second source of truth
   the discharge must re-verify against the context regardless, so (b)
   is churn with zero soundness gain. "The right way + mirror z3" =
   keep the var table in the search (done), keep the proof obligation
   in the context (a).
2. **The intBranch payload.** Current: `(x : Var, v : Rat)` — but the
   branched var's sample is ALGEBRAIC and may be IRRATIONAL (an int
   var assigned a √2-grade witness is reachable: the witness ladder is
   is_int-blind). No `Rat` `v` can represent that sample — the
   `v : Rat` payload is a latent coverage hole, and the discharge
   only ever uses `⌊v⌋`. PROPOSED: change the payload to `(x : Var,
   lo : Int)` — exactly what z3 puts in the emitted clause (the only
   consumer-facing content). Side effect: **R-iv DISSOLVES** — the
   `v.den ≠ 1` condition was predicated on `v` being the sample; with
   `(x, lo)` every payload is sound (any integer lo splits), so
   `grammarOK` stays unconditionally true on intBranch, now by design
   with the reason recorded. Foreign-trace garbage `lo` degrades to a
   valid-but-useless split, never unsound.
   **RESOLVED (Danielle, 2026-08-13): option 1** ("cover every case no
   matter how rare; do exactly what z3 does wherever possible").
3. **Branch-clause flag shape.** z3 adds them `learned=false`; our
   walk treats any bundle-carrying clause as derived. Keep z3's flag
   (fidelity) + the contract exclusion above. The alternative
   (learned=true) would misrepresent z3's clause lifecycle (branch
   clauses are never garbage-collected as learned clauses are — not
   that we port GC).
4. **Tighten loop fidelity.** Port z3's one-at-a-time
   `while (v > lo+1) lo++` verbatim (algebraic compare per iteration,
   refinement-threaded) — NOT a direct floor-via-refine-to-width-1
   (cheaper in principle, but not what z3 does; the loose-bound blowup
   z3 risks is bounded by the same witness-selection intervals in
   both). Perf watch at nla-16.

**Slice plan:**
- **Slice 0 (recon, DONE this session):** source anchors above +
  solver/RAlg/trace seam inventory + the peek_in_complement and
  `!is_int(vlo)` non-divergences documented.
- **Slice 1 — search side:** `RAlg.isInt` (one-liner per the recon);
  `searchCheck` becomes z3's loop (scan in internal order 0..n,
  intLt + tighten with CellM-threaded compares, collect-all, one
  initSearch, per-var clause emission via noteStep/mkClause/
  flushTrace, re-enter search); payload change per decision 2 (ripple:
  Trace.lean grammarOK/isV0 docs, scratch_dump ppStep, the WalkTests
  gate guard). Driver: a small integer UNSAT core that z3's B&B
  refutes (e.g. `{x² = 2}` over one int var — witness ±√2 non-integer
  → branch → both sides die at stage 0... exact driver pinned at
  implementation from live dumps).
- **Slice 2 — checker side:** nodeFSet/buildFSet intBranch arms (F-set
  contribution + context-integrality discharge per decision 1, the
  `n ≤ lo ∨ n ≥ lo+1` omega close via the value-level decode idiom);
  input-contract exclusion; gate lift (isV0 drops the intBranch arm →
  all shapes v0; nodeFSet throw arm DELETED — no non-v0 shapes
  remain); Walk.precheck mirror.
- **Slice 3 — tests + close-out:** integer driver walked end-to-end
  (search → trace → `nlsat_refute`); F-w probes (missing integrality
  hyp → sound reject; garbage-lo foreign payload → still-sound split
  pin; grammar docs); the two existing WalkTests intBranch guards
  updated to the new payload; G6 row flip; HANDOFF rewrite; memory.

**Roadmap context after 12e (unchanged):** nla-14 (the tactic —
12e's integrality-hyp convention is exactly the frontend seam it will
own) → nla-15 → nla-16 = M6.
