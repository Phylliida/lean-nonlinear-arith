## ## nla-12d `active` (opened 2026-08-01) — explain: the projection port

Source of truth: `git show z3-4.12.5:src/nlsat/nlsat_explain.{h,cpp}`
(1914 lines; levelwise does not exist at 4.12.5 — the classic
Jovanović–de Moura projection is the WHOLE file). Same-arc twin:
nla-19a (trace payloads pin only when the checker consumes them —
standing rule 3). Explain lives behind the already-live `ExplainFn`
boundary (`Solver.lean:791`, `Array Literal → SolverM (Option (Array
Literal))`, consumed by `resolveLazyJustification` :849); mockExplain
stays as the test mock (faithful for boolean + stage-0 conflicts).

**Interface audit (12d.0, DONE 2026-08-01):** the nra path touches
explain at exactly four points — construction (nlsat_solver.cpp:239),
updt_params flags (:276-278), set_full_dimensional in check() (:1611),
and the single operator() call in resolve_lazy_justification (:1828).
nra_solver.cpp never calls explain directly. Flags on our path:
simplify_cores=TRUE, minimize_cores=FALSE, factor=TRUE,
full_dimensional=dynamic (stored at check() since 12c.6),
signed_project=FALSE.

**Declared non-ports (dead on the nra path at 4.12.5, zero call
sites):** minimize/minimize_core (:1405-1472); the signed_project
cluster (:1604-1806 incl. solve_eq, project_±infinity, project_pairs/
single); maximize (:1808 — dead upstream, and buggy: split_literals →
add_literal with m_result null); public project(var,…) (:1503 —
nlqsat-only: reorder/restore + result-negation duality); keep_p_x
(:559 — dead helper); test_root_literal (:1879, test API); display/pp
printers. **Live and mandatory:** the pseudo-division simplify cluster
(:1096-1341) — simplify_cores=true is the nra default, so it is NOT a
flag case; the pipeline is operator() → process → process2 →
normalize+simplify → main → project(ps, max_x).

**Porting quirks to preserve (from the audit):** m_factor never
ctor-initialized upstream (ours gets a defined default, set from
params); add_literal silently drops false_literal (:186) and asserts
≠ true_literal; root literals always emitted NEGATED (:733) EXCEPT
mk_linear_root encodings, which fold negation into the kind/lsign
remap (LE→GT+negate-lit, GE→LT+negate-lit :869-873); 1-based root
indices; psc returns after the FIRST surviving chain element BUT a
nonzero-constant psc also returns (:652) while vanishing ones continue
with a zero assumption (:656); elim_vanishing walks DOWN variables
(re-peeks the new max var :318-322); add_cell_lits exact-root hit
returns immediately, skipping the upper bound (:937); all_univ early
break skips cell lits for the final stage (:1002-1005); sign-flip
accounting only for negative ODD factors (:440-442, :1132-1137 —
three independent parity tests); atom::flip on rebuilt kinds + literal
negation = double-negation sites (:468-473, :1192-1196); UINT_MAX
sentinels in select_eq (:1272) and add_cell_lits (:910-912).

Slice plan (each lands compiling + pinned, small commits):

- **12d.1 scaffold** `done` (2026-08-01): `Nlsat/Explain.lean` +
  `ExplainTests.lean` — ExplainM monad (per-call state over SolverM;
  z3's imp fields are all per-call scratch except the solver-owned
  cache/flags), addLiteral (:183 — false_literal dropped, dedup by
  index, release-kept true_literal), resetAlreadyAdded, sign (:211 via
  AnumEval.evalSignAt), collectPolys (:241), maxVarPolys (:515 with
  const-poison replication), todo_set (:49-117 — mkUnique = identity
  on canonical MPoly, structural dedup), addSimpleAssumption/
  addAssumption (:286/:294 with the negated-clause-literal polarity),
  ensureSign (:822 active #else branch). Solver gained the
  `ExplainCache` (pscChains/factors memo tables — engines land behind
  them), the `factor` flag (default true), and the reorder
  `m_cache.reset()` hook (:2408 program point; reinit_cache documented
  no-op). 14 pins green, full build green. **Scope amendment:**
  `add_zero_assumption` (:262) needs the factor engine, and the audit
  found z3's `m_cache.factor` → `manager::factor` is a MULTIVARIATE
  `factor_core` (iccp → Yun square-free via multivariate gcd/exact_div
  → per-piece: deg-1 as-is / univariate via nla-27 upolynomial /
  deg-2 discriminant-sqrt attempt / deg>2 multivariate pushed back
  unfactored "TODO Dejan's procedure"), returning DISTINCT factors
  with the constant (incl. sign flips) dropped — that engine is its
  own slice:
- **12d.1b multivariate factor_core** `active` (sub-sliced 2026-08-01;
  **engine decision: FULL mod_gcd — Danielle**): z3's gcd ladder
  (`manager::gcd` :4395) is zero/const/eq cases → `gcd_content` (var
  in only one side) → same-var-set: univariate `uni_mod_gcd` (:3812 —
  big-prime loop + Zp `euclid_gcd` + CRA + `pp(C_star)` candidate +
  divides check, gcd_prs fallback) / multivariate `mod_gcd` (:4300s —
  big-prime loop + `mod_gcd_rec` Zp evaluation/interpolation +
  skeleton cache + CRA, gcd_prs fallback). `m_use_prs_gcd=false`
  hardcoded (:2340) ⇒ mod_gcd is the live route; gcd_prs is the
  documented fallback (ported first — needed by both). Note:
  `uni_mod_gcd`'s inner gcd is polynomial.cpp's Zp-mode `euclid_gcd`
  (→ gcd_prs), NOT nla-27's upolynomial mod_gcd — the Zp layer is
  shared by both modular gcds. The 231-prime table + balanced CRA idiom
  already exist (`Kernel/ZPoly.lean` bigPrimes/craCombineImages —
  univariate; multivariate CRA at :3700s lands in iii).
  - **12d.1b-i ℤ-mode MPoly foundations** `done` (2026-08-01,
    `Nlsat/MPolyOps.lean`): all of the spec + NumMode (mpzzp mode
    flag) generalization — exactDiv/divides/pseudoDivisionCore/
    icStrip/exactDivScalar take `mode := none` defaults (the Zp
    instances serve iii/iv). ModD declared non-port (x2d null on all
    reachable paths). partials registered with nla-31. 40+ pins.
  - **12d.1b-ii gcd ladder ℤ-mode** `done` (2026-08-01,
    `Nlsat/MPolyGcd.lean`): gcdContentM, gcdPrsM (+prsLoop), top
    gcdM with the var-search (zip-find + beyond-sz cases), const/eq/
    zero cases with flip normalization. **QUIRK FOUND + ported
    verbatim + pinned:** uniModGcd's constant-image branch returns
    q = lc_g when d_a = 1 even when lc_g ≠ 1 (gcd(2x+1, 2x+3) = 2 —
    an upstream edge-case bug, reachable when true gcd is 1 but lcs
    share a factor).
  - **12d.1b-iii Zp-mode layer** `done` (2026-08-01,
    `Nlsat/MPolyZp.lean`): managerNormalize (:5781 — Zp balanced /
    ℤ CONTENT-STRIP, both live in mod_gcd), univEval/substitute1/
    mkGlexMonic/lcGlexZpX, NewtonInterpolator, Skeleton +
    SparseInterpolator + LinearEqSolver (Gaussian elim over Zp —
    **submul arg-order bug caught by pins**: ZpCtx.submul is
    (a,b,out) = out−a·b vs z3's (a,b,c,out) = a−b·c), craCombineImagesM
    (differential-pinned vs nla-27 univariate). **peek_fresh ported
    counter-based, registered argument:** z3's rand()%p is libc-rand
    with NO srand anywhere (platform-dependent sequence); every
    sampled candidate is divides-verified before returning, so the
    sample sequence is unobservable in outputs. 25 pins.
  - **12d.1b-iv mod_gcd assembly** `done` (2026-08-01, with ii):
    modGcdRec (min-degree-sorted vars, peek loop with lc_g-val filter,
    dense/sparse InterpState, min_deg_q resets, skeleton save on dense
    success, sparse failures → gcdPrsM via Option), modGcd (bad-prime
    length checks, C_star CRA accumulation + glex-max discard,
    candidate content-strip + lc divisibility + divides verification,
    231-prime exhaustion → gcdPrsM). **mgcd_check differential pins:
    modGcd ≡ gcdPrsM on shared inputs** (z3's own debug check made
    external). Zero-exponent-monomial bucket bug (iccpZpXM emitting
    [(x,0)]) caught by probe hangs. Note: euclid_gcd's univariate
    SASSERT is documentation — called on multivariate contents.
  - **12d.1b-v factor layer** `done` (2026-08-01,
    `Nlsat/MPolyFactor.lean`): MFactors (constant + (poly,mult);
    accConstant/flipSign/push), toZPoly?/ofZPoly conversions,
    ppM/iccpM, factor2SqfPp (flipped_coeffs), factorSqfPpUniv (nla-27
    bridge), dispatch, factorCore (Yun where-loop; the x-param
    where-capture trap), factorM + factorDistinct (constant dropped).
    Explain.factor memo wrapper + addZeroAssumption (zero-sign
    factors only, negated multi-factor EQ). 15 pins incl. Yun
    j-order (P₁ first), deg-2 split order (f1 = 2ax+b−√disc first),
    (x+1)(y+1) content-first order, x³+y³ punt, cache memo shape.
    **12d.1b CLOSED.**
- **12d.1 residual note**: `m_cache.psc_chain` (:231-236) needs a
  MULTIVARIATE psc chain (psc in the top var with MPoly coefficients —
  QPoly.discChain/resChain are univariate-ℚ only); engine lands with
  12d.5 behind `ExplainCache.pscChains`.
- **12d.2 elim_vanishing + normalize** `done` (2026-08-01): both
  arities (walk-down re-peek, nonzero-const-lc stop, zero reduct via
  is_const — the literal k==0 branch is defensive-dead, ported), all
  assumption shapes (EQ / EQ-negated for even factors / LT / GT),
  negative-ODD-factor flips, atom::flip + literal-negation rebuild,
  ps-empty const resolution, false-clears-core. IneqKind.flip into
  Types.lean. 12 pins incl. z3's Example 2 verbatim.
- **12d.3 cell machinery** `done` (2026-08-01): sign, add_cell_lits
  (exact-hit early return, tightest-bound tracking, full_dimensional
  openness, abort image as Option), all_univ. Pins: √2 exact hit,
  two-sided with dedup across bound emissions, one-sided both
  directions, linear bounds ± full_dimensional.
- **12d.4 root-atom creation** `done` (2026-08-01): all three tiers;
  p_diff goes through m_pm.normalize = ℤ content-strip (:803, pinned);
  mk_plinear is NOT in add_root_literal's chain (reachable only via
  the quadratic A-vanishing degenerate — pinned); generic fallback via
  Solver.mkRootAtom only. RootKind.toIneqSign into Types.lean.
  7 pins.
- **12d.5 projection loop + simplify cluster** `done` (2026-08-01):
  psc-chain engine FIRST (MPolyOps: Se_Lazard dichotomous +
  optimized_S_e_1 + psc_chain_optimized — hand-verified chains:
  −8/108/4/[2,1]; **lc-at-own-degree bug in optimizedSE1 caught by
  x⁴+1 probe hang** [defective chains have deg S_{d−1} = e < d−1;
  out-of-bounds → panic-default → div-by-zero loop]). pseudo_remainder
  was already MPoly-level from 12d.1b-i (pseudoDivisionCore).
  Explain-side: todo in ExplainState, addFactors (factor=true path),
  addLc, pscChainCached + psc/pscDiscriminant/pscResultant
  (first-surviving-element semantics), project (degenerate cell-lits
  case, all_univ break). Simplify cluster: EqInfo lc bookkeeping,
  simplifyLit (keep-original on value-true counts as UNMODIFIED —
  pinned), simplifyWithEq, selectEq (**release semantics: d = 0
  lower-stage eqs ARE selected** — z3's SASSERT is debug-only,
  documented), selectLowerStageEq, simplifyCore. 17 pins.
- **12d.6a operator() + production explain** `done` (2026-08-01):
  main/process2/process pipeline (const-poison as UINT_MAX = release
  semantics; minimize cluster stays non-port); `Explain.explain`
  behind the ExplainFn boundary (fresh ExplainState per call = z3's
  per-call scratch). Real removeLearnedRoots + delClause
  (Clause.deleted + deattach; skip-deleted at canReorder/
  collectVarInfo/reattachArithClauses; ids stable, no cid recycling).
  **Fragment gate DECISION (documented in Explain.lean): NOT an
  explain-side abort — z3's projection is degree-generic; the gate
  marks the TRACE (12d.6b/19a), the search stays z3-faithful.**
  ACCEPTANCE PINS: x²+y²<0 refuted end-to-end by the real projection
  (zero assumption at x:=0, cell bounds at x:=±1, stage-0 core
  conflict), multivariate SAT green, stage-0 pin re-green with the
  production explain, removeLearnedRoots deletion/deattach.
- **12d.6b trace emission** `todo` (with 19a): `Nlsat/Trace.lean`
  (8-shape), emission points inside explain (operator wrap, cell
  lits, Thom, linear encodings, pseudo-division, factorSplit via
  add_zero_assumption/add_factors, resolution glue at the solver),
  fragment-gate marking (generic root-atom fallback ⇒ S1-gated),
  the trace egress design question (pins HERE — DECIDED 2026-08-03,
  see the F1–F5 block in the nla-19a entry: buffer + per-clause
  bundles, checker-computed gate, emit-all-shapes-now).

Acceptance (arc, shared with 19a): end-to-end on hand goals with
algebraic cells (√2-grade), negative probes (corrupted trace
rejected), first search→trace→checked-theorem round trip. Estimate
3–4 sessions for the arc (DESIGN-endgame §7).

