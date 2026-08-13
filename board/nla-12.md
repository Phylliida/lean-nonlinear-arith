- **nla-12** `active` (lane opened 2026-07-26; slice plan + module map +
  trace language + discharge map in **DESIGN-nlsat-quadratic.md**) nlsat
  search port (classic path of nlsat_solver.cpp / nlsat_explain.cpp; no
  levelwise). Emits traces in the 5-shape language (DESIGN.md section
  2/L3) + integer branch splits. The search is generic in degree; the
  quadratic fragment (deg ≤ 2 per top variable) is enforced at
  explain/check time — S1-free per the one-identity insight
  (`4a·p = (2ay+b)² − disc`). Done so far: **S3 Thom kit**
  (`Templates/Quadratic.lean`, sorry-free: sign dictionary iffs both
  lead signs, definite disc≤0 cases, the 4-lemma point-vs-root-interval
  ordering family + roots-order; mirrors mk_quadratic_root
  nlsat_explain.cpp:886) and **mini-anum** (`Kernel/RAlg.lean` +
  tests: rat|root representation, compare with gcd common-root fast
  path + fueled refinement separation, sign / signOfPolyAt via Tarski,
  ratBetween for witness picking; mkRoot normalizes linear→rational for
  Z3's rational-preference parity). **nla-12a DONE (same day):**
  `Nlsat/Types.lean` (Literal/IneqAtom w/ parity-tagged factors/RootAtom
  per nlsat_types.h; sparse ℚ MPoly with univariate view + QPoly
  bridge) + `Nlsat/IntervalSet.lean` (the mk_union nine-case sweep
  transcribed 1:1 incl. justification-preserving splits,
  same-justification-only compression, slack/full computation;
  pickInComplement deterministic preference ladder: zero → int above →
  int below → gap rational → shared rational endpoint → irrational
  witness; declared divergences: am.select dyadic niceness, rational
  values in root representation). Tests pin union cases + the full
  preference ladder. Trace.lean deferred to 12d (payloads pin when the
  checker consumes them, per design). **anum decision (Danielle,
  2026-07-26): Z3's actual shape, similarity uncompromised** — full spec
  in DESIGN-nlsat-quadratic §4b. **nla-12b-i DONE (same day):**
  `Nlsat/AnumEval.lean` — exact-Rat interval arithmetic w/ even-power
  tightening + MPoly enclosure evaluation; `resultantElim` (the ONE
  resultant shape both call sites need: second argument is always a
  univariate rational defining poly — multiplication-matrix det mod
  monic q̂, faithful lc/sign scalars); `nonzeroRootLowerBound`
  (reverse-Cauchy 2^−k); RAlg interval accessors + width-gated
  refinement. Tests pin the classic eliminations (√2 minimal poly, √6,
  √2+√3 → x⁴−10x²+1, non-monic scaling). **nla-12b-ii DONE
  (2026-07-28):** `Nlsat/Evaluator.lean` — `evalSignAt` (:2246:
  optimistic → rational-fragment substitution → magnitude-gated
  interval refinement → exact resultant zero test with `L = 2^{−k}`,
  nla-28 threaded incl. `save_intervals` restore semantics);
  `isolateRootsAt` (:2547: shortcuts → substitute → stable degree-sorted
  resultant elimination → kernel isolation → `filter_roots`;
  `var_degree_lt`'s UINT_MAX-for-unassigned caught and ported — the
  target sorts last); `isolateRootsSigns` (:2902: refine to
  DEFAULT_PRECISION=2, `intLt`/`select`/`intGt` samples as rational
  defaults). `Nlsat/EvaluatorTable.lean` — `SignTable` (merge with
  nla-28 compare threading, add/addConst/signAt linear branch — binary
  branch is value-identical, declared non-divergence), `satisfied`*,
  `evalIneq`/`evalRoot` (undef-share threading caught: the target's
  value is re-attached after isolation), `infeasibleIntervalsIneq`
  (cell sweep; **review catch: `neg` must feed `satisfied` in the
  sweep**, first pass dropped it) + `infeasibleIntervalsRoot` (the
  ROOT_EQ/LT/GT/LE/GE case table). **q ≡ 0 fallbacks → nla-29**
  (Danielle 2026-07-28: full anum-arithmetic arc first — they need
  anum VALUES). 26 pins green incl. resultant zero test, ±2^{1/4}
  through eliminate→isolate→filter, q≡0 → none, sign-table sweeps
  both variants, eval predicates.
  **CELL-STORE REFACTOR (2026-07-28, post-12b-ii design review,
  Danielle-approved):** z3's two statefulness mechanisms mapped to two
  layers — op level stays the nla-28 tuple ops in RAlg (untouched),
  owner level (x2v, interval endpoints, undef/ext sharing, trail)
  becomes `Kernel/CellStore.lean`: `CellStore = Array RAlg` +
  `CellM = StateM CellStore`, in-place updates so became-basic and
  refinement are visible to every holder (versioned ids would have
  reintroduced the threading bug). `IntervalSet` endpoints and
  `Assignment` bindings are `CellId`s; the nla-28 write-back machinery
  collapsed into store semantics (mkUnion returns just the union again;
  `evalRoot`'s re-attachment hack deleted — that bug class is
  structurally impossible). All pins re-derived and green. TWO STORE-ERA
  LESSONS: (a) `CellId`s dangle outside the store that allocated them —
  test helpers that build sets in separate `run'` calls then mix them
  read out-of-bounds (panic-returns-default, F7 again); every mixed-set
  scenario runs in ONE `CellM` computation. (b) `fresh` written as
  `let s ← get; set (s.push c); return s.size` keeps `s` borrowed
  across the push → RC>1 → full array copy per allocation → quadratic
  blowup in allocation-heavy loops (the mkUnion differential went 7s →
  >300s); write it `let n := (← get).size; modify (·.push c); return n`
  and avoid per-probe allocations (root-vs-rat compares are
  mutation-free → pure reads).
