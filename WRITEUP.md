# WRITEUP — the nlsat explain port (nla-12d), 2026-08-01

*Session arc: nla-12d from planning through 12d.6a. The projection
engine of z3's nlsat — `nlsat_explain.cpp` @ **4.12.5** — is now
ported, pinned, and operational: the production `Explain.explain`
sits behind the solver's `ExplainFn` boundary and refutes real
multivariate conflicts end-to-end. This document describes what was
built, the decisions taken, the quirks preserved, and the bugs the
pins caught. Source of truth throughout:
`git show z3-4.12.5:src/nlsat/nlsat_explain.{h,cpp}` (1914 lines),
never the working tree (4.16-nightly, materially different).*

## 0. What explain is, and why this arc mattered

nlsat's solver finds conflicts by assigning variables to algebraic
witnesses; when a conflict occurs at stage `x`, the *explain*
procedure projects the conflict literals onto the lower stages —
producing new literals (sign assumptions, cell bounds, root
conditions) that, together with the negated core, form the learned
theory lemma. Without it the solver is a model-finder only: every
multivariate UNSAT answer flows through this projection. The arc's
keystone pin: `x² + y² < 0` refuted end-to-end — zero assumption at
`x := 0`, cell bounds at `x := ±1`, stage-0 core conflict, UNSAT.

The search side (everything in `Nlsat/`, `Kernel/`) is **untrusted**:
a bug costs completeness (a failed certification downstream), never
soundness. The trusted consumer of explain's *traces* is 19a's
checker — the next arc.

## 1. The interface audit (12d.0)

Before writing code, the whole 1914-line file was mapped against its
callers. Findings, all registered in BOARD.md:

- The nra path (the only one tactus uses) touches explain at exactly
  four points: construction (`nlsat_solver.cpp:239`), `updt_params`
  flags (:276-278), `set_full_dimensional` inside `check()` (:1611),
  and the single `operator()` call in `resolve_lazy_justification`
  (:1828). `nra_solver.cpp` never calls explain directly.
- Flags on our path: `simplify_cores=true`, `minimize_cores=false`,
  `factor=true`, `full_dimensional=dynamic`, `signed_project=false`.
- **Declared non-ports** (dead on the nra path at 4.12.5): the
  minimize cluster (:1405-1472), the entire signed_project cluster
  (:1604-1806), `maximize` (:1808 — dead *and* buggy upstream:
  `split_literals` → `add_literal` with `m_result` null), public
  `project(var,…)` (:1503, nlqsat-only), `keep_p_x` (:559),
  `test_root_literal` (:1879), all display/pp printers.
- **Consequence:** the pseudo-division simplify cluster (:1096-1341)
  is *live*, not a flag case — `simplify_cores=true` is the nra
  default. The full pipeline is `operator()` → `process` →
  `process2` (`normalize` + `simplify`) → `main` → `project`.
- The **emission grammar** was enumerated from source (the input to
  Q1's coverage proof in 19a): five ineq-atom shapes, three root-atom
  tiers, and the cell-literal forms.

## 2. Architecture

```
Nlsat/Explain.lean     — explain proper (untrusted search-side)
  ExplainM = StateT ExplainState SolverM
  per-call: result literals, already-added dedup, todo set
  solver-owned: ExplainCache (pscChains/factors memo tables),
                flags (simplifyCores, fullDimensional, factor)
Nlsat/MPolyOps.lean    — polynomial manager ops + NumMode (ℤ/Zp)
Nlsat/MPolyZp.lean     — Zp-mode layer + interpolators + CRA
Nlsat/MPolyGcd.lean    — the multivariate gcd cluster (one mutual block)
Nlsat/MPolyFactor.lean — factor_core (iccp + Yun + per-piece dispatch)
```

Design choices:

- **`ExplainM = StateT ExplainState SolverM`** — z3's `imp` persists
  across calls, but all its mutable fields are per-call scratch
  (`m_result`, dedup bits, `m_todo`, buffers). The only cross-call
  state is the solver-owned cache and flags. So explain state is a
  fresh record per `operator()` call, and the production entry is
  `Explain.explain : ExplainFn := fun lits => (operator lits).run {}`.
- **`mk_unique = identity`** — z3 hash-conses polynomials so `pm.id`
  gives stable dedup keys; our MPoly is canonical (eager lex-sorted),
  so structural equality *is* the key. Memo tables are structural
  scans (atom-table idiom: creation-side, not hot).
- **`NumMode = Option ZpCtx`** — z3's mpzzp manager shares one
  polynomial representation and one algorithm set between ℤ and Zp
  modes (a mode flag on numeral ops). Mirrored by parameterizing the
  numeral-touching ops (`exactDiv`, `divides`, `pseudoDivisionCore`,
  `icStrip`, …) with `mode := none` defaults.
- **Skeletons/interpolators are per-`modGcd` state** — z3 resets
  skeletons per `mod_gcd` call and the interpolators' first iteration
  always resets, so cross-call staleness is unobservable; ours are
  plain locals.

## 3. The factor engine mini-arc (12d.1b) — the hidden iceberg

The scaffold revealed that `m_cache.factor` → `manager::factor` is a
*multivariate* `factor_core`, which needs multivariate gcd, which at
4.12.5 defaults (`m_use_prs_gcd = false` hardcoded) to the **full
modular route**. Danielle's call: port `mod_gcd` completely rather
than only the `gcd_prs` fallback. Five sub-slices:

- **i — MPoly foundations:** monomial div/sqrt/pw, glex extremal
  terms, derivative, integer content (const keeps the *sign*), exact
  division and `divides` by glex-max reduction, the
  `pseudo_division_core` family (`exactPseudoRemainder` /
  `pseudoRemainder` instantiations; z3 leaves `d` at the iteration
  count), the sqrt attempt.
- **iii — Zp layer:** `managerNormalize` (balanced reps in Zp mode,
  *integer-content strip* in ℤ mode — both meanings live in mod_gcd),
  eval/substitute/monic, `lcGlexZpX`, Newton + sparse interpolators
  with skeleton and a Gaussian-elimination solver, multivariate CRA
  (differential-pinned against nla-27's univariate one).
- **ii+iv — the gcd cluster** (one `mutual` block): `iccpM`
  (quick-filter: a pure `x^k` monomial with no mixed partner forces
  content 1; gcd-of-coefficients chain with const early exit), the
  `gcdM` ladder (zero/eq/const → `gcdContentM` → univariate
  `uniModGcd` / multivariate `modGcd` / PRS fallback), `euclidGcdM`
  (its univariate SASSERT is documentation — called on multivariate
  contents), `iccpZpXM` (min-degree strip / cheap / bucket paths),
  `modGcdRec` (dense Newton vs skeleton-sparse interpolation,
  `min_deg_q` resets, skeleton save on dense success, divides-
  verified candidates), `modGcd` (bad-prime skips, CRA accumulation
  with the glex-max discard rule, 231-prime exhaustion → PRS).
- **v — the factor layer:** `MFactors` (constant + (poly, mult)
  pairs; sign flips fold into the *dropped* constant), `factorCore`
  (iccp + Yun), per-piece dispatch (deg-1 as-is / univariate via
  nla-27's `Factor.factorSquareFree` / deg-2 discriminant-sqrt with
  `flipped_coeffs` bookkeeping / deg > 2 multivariate **punted back
  unfactored — z3's own "TODO: Dejan's procedure"**), and the cache
  view: distinct factors, constant dropped.

## 4. The projection (12d.2–12d.6a)

- **12d.2** `elim_vanishing` (strips coefficients that vanish under
  the current assignment; vanishing non-const lcs become zero
  assumptions; walks *down* to the reduct's new max var) and
  `normalize` (eliminates vanishing leading coefficients and
  lower-stage factors from core literals, with sign assumptions;
  sign flips only for negative *odd* factors; `atom::flip` +
  literal-negation rebuild; const-resolution to true/false literals;
  a false literal *clears the whole core*).
- **12d.3+12d.4** `add_cell_lits` (exact-root hit ⇒ single
  `¬ROOT_EQ` and immediate return; else tightest root bounds
  `¬ROOT_GT`/`¬ROOT_LT`, GE/LE under full_dimensional; 1-based root
  indices) and the root-atom tiers: linear const-lc → plain ineq atom
  with the LE/GE kind-remap folding the negation; quadratic → Thom
  encoding (pure sign literals on `{disc, A, 2Ay+B, p}`, with `p_diff`
  going through `m_pm.normalize` = **ℤ content-strip**, and the
  A-vanishing degenerate falling to `mk_plinear_root`);
  generic fallback via `Solver.mkRootAtom`, always negated.
  (`mk_plinear_root` is *not* in `add_root_literal`'s chain —
  reachable only via the quadratic degenerate. Pinned.)
- **12d.5** the psc-chain engine (`Se_Lazard` dichotomous +
  `optimized_S_e_1` + `psc_chain_optimized` — chains hand-verified
  against analytic resultants: `Res(x²−2, 2x) = −8`,
  `Res(x³−2, 3x²) = 108`, `Res(x²+1, x²−1) = 4`,
  `Res(x⁴+1, x³+1) = 2` with chain `[2, 1]`), the projection loop
  (`add_lc`, `psc` with its first-surviving-element semantics —
  nonzero-const returns too, vanishing ones continue with a zero
  assumption — `psc_discriminant`, `psc_resultant`, `add_factors`
  with `factor=true`), and the **simplify cluster** (equation
  selection, pseudo-division rewriting with three independent parity
  tests, lc ineq/diseq bookkeeping, the keep-original/emit-direct
  cases below `max`).
- **12d.6a** the `operator()` pipeline (`main` → `process2` →
  `process`; const-poison carried as concrete `UINT_MAX` = z3's
  release semantics), the production `Explain.explain`, and real
  `removeLearnedRoots` + `delClause` (the 12c carry-over: learned
  clauses with root atoms are deleted before reorder's rename).

## 5. Key decisions (all registered)

- **Full `mod_gcd`** (Danielle, over `gcd_prs`-only): the modular
  route with big primes, Zp evaluation, interpolation, skeletons —
  ~4 sessions of engine for exact mechanism fidelity.
- **`peek_fresh` ported counter-based.** z3 draws `rand() % p` — libc
  `rand()` with *no `srand` anywhere in z3's source*, i.e. the
  sequence is platform-libc-dependent (z3 itself is not
  cross-platform faithful here). Registration argument: every sampled
  candidate is verified by `divides` before returning, so the sample
  sequence is unobservable in outputs (also restores the determinism
  directive).
- **The fragment gate is not an explain-side abort.** z3's projection
  is degree-generic; out-of-fragment steps (the generic root-atom
  fallback, degree ≥ 3) will *mark the trace* as S1-gated at
  12d.6b/19a. The search stays z3-faithful; the gate is a trace
  property, not a search property.
- **Release semantics over debug asserts**, uniformly: `select_eq`
  selects degree-0 (lower-stage) equations (its `SASSERT(d > 0)` is
  debug-only); const-poisoned `max_var` computations carry
  `UINT_MAX`; `euclidGcdM` accepts multivariate inputs.
- **An upstream edge-case quirk, ported verbatim and pinned:**
  `uniModGcd(2x+1, 2x+3) = 2` — the constant modular image branch
  returns `lc_g` when `d_a = 1`, although the true gcd is 1
  (:3869-3873; reachable when the true gcd is 1 but leading
  coefficients share a factor).

## 6. Bugs the pins/probes caught (each now pinned)

- **`ZpCtx.submul` argument order** (its `(a,b,out) = out − a·b` vs
  z3's `(a,b,c,out) = a − b·c`) — Gaussian elimination solved wrong
  systems; caught by the solver pins.
- **Zero-exponent monomials** (`[(x, 0)]`) constructed in two places
  (iccpZpX buckets, an early `optimizedSE1` H-row) — violates the
  monomial invariant, loops downstream. Both now use `ofVarPow`.
- **`optimizedSE1` lc-at-wrong-degree** — defective chains have
  `deg S_{d−1} = e < d−1`; indexing `[d−1]` ran out of bounds →
  panic-returns-default → division by zero → infinite loop, caught by
  the `x⁴+1` probe hang. lc is at the poly's *own* degree.
- **`mgcd_check` made external:** z3's debug-only differential
  (modGcd ≡ gcdPrs) is a permanent pin suite.

## 7. Verification status

- Full build green: **7600 jobs**, sorry-free, trusted layer untouched
  (all new code is untrusted search-side).
- ~150 new `#guard` pins across `MPolyOpsTests`, `MPolyZpTests`,
  `MPolyGcdTests`, `MPolyFactorTests`, `ExplainTests`, including:
  z3's own Example 1/Example 2 from the source comments verbatim;
  the clause-polarity convention (assumptions appear *negated* in the
  output clause); hand-computed psc chains; the quirk pin; dedup
  across cell-bound emissions; the x²+y²<0 acceptance.
- All prior suites re-green (12c solver pins, evaluator, kernel).

## 8. Commit log (the arc)

| Commit | Content |
|---|---|
| `fb99f8c` | 12d+19a boarded: slices, audit, non-port register |
| `72d197f` | 12d.1 scaffold (ExplainM, todo_set, assumptions, caches) |
| `9ecb07e` | 12d.1b sub-sliced: full mod_gcd decision |
| `407db61` | 12d.1b-i MPoly foundations |
| `6db7fa1` | 12d.1b-iii Zp layer + interpolators + CRA |
| `05f4aad` | 12d.1b-ii/iv the gcd cluster |
| `d4812c6` | 12d.1b-v factor layer + `addZeroAssumption` |
| `d477ef3` | BOARD: 12d.1b closed |
| `f9e4102` | 12d.2 elim_vanishing + normalize |
| `9070840` | 12d.3+12d.4 cell machinery + root atoms |
| `c31940f` | 12d.5 psc engine + projection loop + simplify cluster |
| `1e2ff57` | 12d.6a operator() + production explain + del/removeLearnedRoots |
| `6ba868d` | BOARD: slices marked, 12d.6b scoped |

## 9. What remains (see HANDOFF.md)

12d.6b ⇄ 19a: `Nlsat/Trace.lean` (the 8-shape trace language with
emission points and the S1-gate marking) and `Nlsat/Check.lean` v0
(the trusted discharge map: leafNumeric → nla-09 certificates,
thomQuadratic/linearRoot/cellBound → the S3 quadratic kit) plus the
Q1 grammar-first S3-coverage proof. Then 19b (full checker glue →
**M3**), 12e (integer branching), 14 (the `nonlinear_arith` tactic),
15 (tactus wiring), 16 (parity harness).
