## nla-31 `todo` — termination proofs for the analytic walks/loops (Danielle, 2026-07-31)

The remaining `partial` defs in the anum layer, with the shape of each
argument. Danielle's directive: build and PROVE the termination
arguments properly.

- **`mkBinary`/`mkUnary` loops**: each iteration strictly halves both
  isolating intervals (or exits became-basic). The target factor's
  `V ≥ 1` at every iteration (its root is strictly inside `r_i` by the
  non-root-endpoint invariant); distinct factors have distinct roots
  (factorization correctness), so once the interval is narrower than
  every root-gap the scan yields a unique `V == 1`. Needs: correctness
  of `Factor.factor` (product of distinct square-free factors ∼ p, no
  shared roots), Sturm count correctness (**nla-10**), root separation
  (square-free ⇒ nonzero minimum gap).
- **`isolating2Refinable` walks** (cases 2–4): the halving walk reaches
  a point whose sign differs from the endpoint sign (or the exact
  root). Existence of that point follows from the `V == 1` count +
  square-freeness (the root is simple, so the sign changes across it) —
  same nla-10 flavor.
- **`refineNzBound` walks**: sign stability of a polynomial near a
  NON-root point — elementary (continuity-style: `p(0) ≠ 0` ⇒ sign
  eventually constant on the halving sequence); does NOT need Sturm.
  Cheapest of the bunch, do first.
- **Pre-existing partials in the same class** (include in scope):
  `Mpbq.refineUpper`/`refineLower` (dyadic grid finer than
  `|q − dyadic|` with `q` non-dyadic), `refineToPrecD` (width gate
  halves), `compareCore`'s loops, `separate`, `selectSmallCore*`,
  `BivPoly.detBivLaplace` (structural on matrix size — actually easy:
  recursion on `n`).

Sequencing: the elementary ones (refineNzBound, refineUpper/Lower,
detBivLaplace) are independent; the Sturm-flavored ones (mkBinary,
mkUnary, isolating2Refinable) compose with nla-10.

The `q ≡ 0` degenerate fallbacks inside `isolateRootsAt`
(`algebraic_numbers.cpp:2622-2678`: linear-coefficient solve with anum
division, and the auxiliary-z nested path with anum coefficient
evaluation) need anum VALUES — z3's op-by-op algebraic-number
arithmetic: `imp::eval` over `add`/`mul` (both `mk_binary` —
resultant-composed defining polynomial + interval disambiguation),
`neg` (`p_minus_x` + interval negation), `inv` (`p_1_div_x` + rational
interval inversion + `convert_q2bq_interval`), `div` = inv+mul. Port
faithfully (Danielle's call over a resultant-chain shortcut: full
mechanism, no case harder for us than for z3). Then land the two
fallbacks with z3's exact shape, and `isolateRootsAt`'s `none` case
disappears. Sequence: before 12c's conflict path (the solver's
`eval_root`/`infeasible_intervals` hit degenerate traces there).
[medium-large: own arc]

Slice plan (2026-07-31, source-anchored to algebraic_numbers.cpp unless
noted; 29.1 decision resolved below):

- **29.1 kernel gadgets** `done` (2026-07-31): `QPoly.pMinusX` /
  `p1DivX` / `composeAnPXDivA` / `translateQ` / `composePQX` in
  `Kernel/QPoly.lean` (verbatim ports, z3's positive scalar factors
  preserved); `convertQ2BqInterval` in `Kernel/Roots.lean` (returns
  `Mpbq ⊕ (Mpbq × Mpbq)` — `.inl` = exact-root discovery during the
  walk, which z3 reports as `false`+root-in-`c`; 29.3 call sites treat
  it as became-rational); `Kernel/BivPoly.lean` ((ℚ[x])[y] dense,
  `composeXMinusY`/`composeXPlusY` Horner, `composeXDivY` direct,
  `modMonic`/`powModTableB`, `detBiv` Laplace — exact over the ring
  ℚ[x], exponential in d = deg pb, nla-30 if deep nesting demands
  Bareiss; `resultantElimY` = lc(pb)^degF·det, NO parity factor per the
  25.3 lesson). Pins: hand-traced z3 walks (4/3 → c=11/8 d=3/2;
  7/5..10/7 → 721/512, 91/64; walk root-hit .inl 3/8) + √2+√3 ↦
  x⁴−10x²+1 (differential vs the AnumEval pin), √2·√3 ↦ (x²−6)²,
  non-monic 4x⁴−28x²+1, linear, (x²−4)². Original slice text kept:

  Original scope: `pMinusX` (p(−x), odd-coeff sign flip — `p_minus_x`, used by neg
  :1784); `p1DivX` (x^n·p(1/x) = coefficient reversal — `p_1_div_x`,
  used by inv :1847); `translateQ` (p(x−q) Taylor shift — `translate_q`
  :1608, algebraic+basic add); `composePQX` (q^n·p(x/q) —
  `compose_p_q_x` :1716, algebraic×basic mul); `convertQ2BqInterval`
  (rational interval → tight dyadic bracket — upolynomial.cpp:2833;
  inv and both mixed basic/algebraic paths funnel through it).
  Bivariate resultant shapes for mk_binary: represent (ℚ[x])[y] as
  `Array QPoly` (poly in y with QPoly coeffs); `composeXMinusY` /
  `composeXPlusY` (mk_add_polynomial :1000-1019) and `composeXDivY`
  (y^n·pa(x/y), mk_mul_polynomial :1028-1044), then eliminate y against
  the univariate pb(y). **Decision (Danielle, 2026-07-31): extension
  APPROVED** — the capability sets are identical on every reachable
  input (both routes compute the exact mathematical resultant; the
  determinant identity `Res(f,g) = lc(g)^{deg f}·det(mult-by-f mod ĝ)`
  is a theorem, not an approximation, valid for all f and all pb with
  deg ≥ 1). The only inputs z3's general multivariate resultant handles
  beyond this are multivariate second arguments, which no reachable
  call site produces (the second argument is always a univariate
  defining poly). Deferred-generality work recorded as **nla-30**.
- **29.2 mk_binary/mk_unary engine** `done` (2026-07-31, engine half):
  `Kernel/AnumArith.lean` — `mkBinary` (:1210) verbatim: resultant-composed
  poly (BivPoly route) → nla-27 factor → per-factor `sturmChain` (|lc|-
  normalized; positive rescaling preserves the V counts) → discard/target
  scan with the UINT_MAX analogue → `setCore` (:1150: zero-snap via
  `signVarAt seq 0`, zero-strip, new `isolating2Refinable` in Roots.lean —
  all 4 cases) → refine with z3's short-circuit `!refine(a) || !refine(b)`
  became-basic re-dispatch. `save_intervals` semantics:
  `restoreIfTooSmall` on BOTH exits (z3's duplicate `saved_a` call at
  :1285-1286 is a no-op; saved_b is restored by its destructor — net
  effect both, ported as both). mk_unary NOT ported: only serves k-th
  roots/powers (:1550/:1580), unreachable from our op set. MpbqI moved
  Nlsat/AnumEval → Kernel/Mpbq (mk_interval functors need it; resolves
  via the existing `open`). Original slice text kept:

  Original scope: factor
  (nla-27) → sturmChain per factor → signVarAt at r_i endpoints →
  discard/target loop (V≤0 discard, V==1 target, else keep) →
  refine a/b with became-basic re-dispatch to mk_basic
  (add_proc/sub_proc/mul_proc :1077-1099) → save_intervals /
  restore_if_too_small (nla-28 semantics) → set_core (:1150: interval
  contains 0 ∧ p has zero root ⇒ reset to rational 0; else mkRoot with
  minimal flag + am::normalize zero-straddle). CellM threading
  throughout (refine mutates cells); store-era lessons apply: one
  CellM computation per scenario, `modify`-style fresh, no per-probe
  allocations on mutation-free paths.
- **29.3 the ops** `done` (2026-07-31, with 29.2): dispatch tables
  verbatim in `Kernel/AnumArith.lean` — add/sub (zero shortcuts,
  basic+basic, algebraic+basic via `addAlgebraicBasic` = translateQ with
  to_mpbq fast path + convertQ2BqInterval fallback, algebraic+algebraic
  via mkBinary IsAdd); mul (zero reset, `mulAlgebraicBasic` = composePQX
  with negative-scalar endpoint swap, mkBinary); neg (pMinusX + interval
  negation); inv (`refineNzBound` FIRST — div2 walk with root-hit ⇒
  became basic; then p1DivX + rational endpoint inversion + swap +
  convertQ2BqInterval); div = inv + mul on a COPY of the divisor (b never
  mutated). Two declared z3-bug-side treatments (verdict-preserving, in
  the file header): (1) add/mul mixed-path convert exact-root ⇒ z3 logs
  "conversion failed" and calls set with a STALE upper bound (:1629/:1742)
  — we return `.rat` of the found root (the value IS that dyadic);
  (2) inv's convert exact-root ⇒ z3 THROWS (:1858), aborting the nlsat
  call — we return `.rat` (can only continue where z3 fails, never the
  reverse). Division-by-zero is UNREACHABLE in z3 (throws); our callers
  pre-discharge ≠0 (29.5's linear solve checks `!is_zero(a1)` first) —
  explicit precondition, no panic-guard reliance (F7 lesson).
  Pins (AnumArithTests): √2+√3 .eq to the isolated x⁴−10x²+1 cell,
  √2·√3 = √6 .eq, √3−√2 small root, neg/inv/div, non-dyadic mixed paths
  (√2+1/3, √2/3), and the DESIGNED became-basic pin: x²−4 cell (1,3) +
  −√3 cell (−32,−1) — sum interval covers both result factors so the
  first scan leaves 2 candidates, first refine bisects at exactly 2 ⇒
  a' == .rat 2 persisted, result 2−√3. CellStore lifts addC/subC/mulC/
  negC/invC/divC pinned through the store. Original slice text kept:

  Original scope: (:1584-1883), dispatch tables verbatim: add/sub
  (zero shortcuts, basic+basic, algebraic+basic via translateQ with
  to_mpbq fast path + convertQ2BqInterval fallback, algebraic+algebraic
  via mk_binary IsAdd); mul (zero reset, basic scaling via composePQX
  with negative-scalar endpoint swap, mk_binary); neg (pMinusX +
  interval negation + update_sign_lower); inv (refine_nz_bound FIRST
  :1794-1833 — div2 walk until endpoint sign matches cell sign, root
  hit ⇒ becomes basic; then p1DivX + rational endpoint inversion + swap
  + convertQ2BqInterval); div = inv + mul (:1868). Division-by-zero is
  UNREACHABLE in z3 (throws); our callers pre-discharge ≠0 (the 29.5
  linear solve checks `!is_zero(a1)` first) — mirror as an explicit
  precondition, no panic-guard reliance (F7 lesson).
- **29.4 imp::eval walker** `done` (2026-07-31): `evalAnum`/`evalCore`
  in `Nlsat/Evaluator.lean` — `t_eval`/`t_eval_core`
  (polynomial.cpp:6676/6749) verbatim: Horner over the max var with
  recursive coefficient evaluation (`maxSmallerThan` =
  polynomial::max_smaller_than), group splitting on x-degree drops,
  single-monomial ascending-var walk. z3 lex-sorts first; our MPoly is
  already canonical (approved eager-sort). Stored-cell refinements
  persist via the ops' write-backs (z3 reaches them through the public
  const_cast wrappers — probe-confirmed :3268-3300: the "const&" ops
  mutate); temps are overwritten per op in both worlds, so no temp
  threading. Required `RAlg.power` (z3 `power` :1559 via a new
  `mkUnary` engine in AnumArith.lean — this board's earlier "mk_unary
  unreachable from our op set" note was WRONG: t_eval's
  `vm.power(x2v(y), d, …)` reaches it; `xMinusYPow` =
  resultant_y(x−y^k, pa(y)), `MpbqI.pow` interval, power_proc
  re-dispatch).
- **29.5 q≡0 fallbacks in isolateRootsAt** `done` (2026-07-31): linear
  solve (eval c0/c1; a1 == 0 ⇒ no roots; else root = −a0/a1 via
  div+neg); auxiliary-z (first non-vanishing coefficient scan i = n..1;
  all vanish ⇒ no roots; else q2 = z·xⁱ + (p' capped at x-degree i−1),
  z ↦ a, nested call with the flag — `partial`, z3 caps nesting at one
  level by SASSERT). `none` survives only for the z3-SASSERT-violation
  case (nested ∧ q ≡ 0). WITNESS ANALYSIS (corrects the acceptance
  sketch below): q ≡ 0 needs ONE factor F of the (square-free, possibly
  reducible) defining poly d dividing EVERY x-coefficient of p'; if F's
  root IS the assigned value, all coefficients vanish (the no-roots
  case); if it is a DIFFERENT factor's root, none vanish and aux-z
  fires with i = n. The "(y²−2)·x² + x + c ⇒ aux-z z↦1" sketch was
  wrong — the resultant does not vanish there (normal path handles it).

Acceptance pins landed (EvaluatorTests + AnumArithTests): √2+√3 ↦
x⁴−10x²+1 cell (differential vs the AnumEval pin), √2·√3 = √6, −√2,
1/√2, div roundtrip; mixed basic/algebraic √2+1/3 and √2/3 (non-dyadic
⇒ convertQ2BqInterval fallback); the designed became-basic mid-mkBinary
pin (a' == .rat 2 persisted); evalAnum: x²+y² ↦ 5, x·y ↦ √6,
x³−xy ↦ −√2; q≡0 witnesses: x·(y²−2) at √2 ⇒ #[] (the stale `none`
pin updated — z3 returns empty roots there), (y²−3)(x−1) at the
√2-root-of-(y²−2)(y²−3) cell ⇒ root 1 via div+neg, (y²−3)(x²−x−1)
same cell ⇒ aux-z ⇒ exactly {(1±√5)/2} (.eq to isolateRoots of
x²−x−1; the filter drops 0 and ±√(1+√2)), (y²−2)(x²+x+1) at √2 ⇒ #[].

Original acceptance sketch (for the record): √2+√3 lands on an x⁴−10x²+1 cell (differential vs the
AnumEval pin), √2·√3 on the √6 cell, −√2 sign+interval flip, 1/√2,
(a/b)·b ≡ a under compare; mixed basic/algebraic √2 + 1/3 (non-dyadic
basic ⇒ convertQ2BqInterval fallback path); became-basic mid-mk_binary
re-dispatch (one argument discovers rationality during refinement);
q≡0 witnesses: (y²−2)(x+1) at y↦√2 ⇒ no roots (all coefficients
vanish), (y²−2)·x² + x + c at y↦√2 ⇒ auxiliary-z path fires with z↦1
[wrong — see the witness analysis above].

