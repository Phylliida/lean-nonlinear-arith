# nlsat, quadratic-restricted — design (nla-12-restricted + nla-19)

Status: lane opened 2026-07-26. Companion to DESIGN.md §2 (L2/L3); this
document pins the module map, the trace language, the quadratic-fragment
contract, and the discharge map onto the nla-09 bridge + the S3 kit.

Source of truth for fidelity: the classic path of `z3/src/nlsat/*` at the
4.12.5-parity level (levelwise excluded, per DESIGN §4). File references
below are into the workspace checkout `../z3/src/nlsat/`.

## 0. The one-identity insight (why deg ≤ 2 is S1-free)

`mk_quadratic_root` (nlsat_explain.cpp:886) eliminates every root atom on
a quadratic `p = A·y² + B·y + C` by Thom encoding: the learned clause
speaks only of *sign conditions* on `disc = B² − 4AC`, `A`, `p' = 2Ay + B`,
and `p(y)` itself (plus `mk_linear_root` for degree 1, which needs nothing).
All semantic content of those sign conditions flows from a single ring
identity:

```
4·A·(A·y² + B·y + C) = (2·A·y + B)² − (B² − 4·A·C)
```

so for `A ≠ 0` the sign of `p(y)` is the sign of `(2Ay+B)² − disc`
(times sign of `A`), and orderings between Thom-encoded points reduce to
comparisons of `(2Ay+B)²` against `disc` with the sign of `2Ay+B` breaking
the square's symmetry. Cell validity for quadratics is therefore a
*first-order consequence per instance* — completing-the-square lemmas
(S3 kit) + `ring`/`linear_combination` — with no delineability
(S1/continuity) argument anywhere. The numeric univariate leaves (stage 1,
rational coefficients) are exactly the nla-09 bridge's claims.

Fragment contract: **checkable trace = every projection/root step stays at
degree ≤ 2 in its top variable.** The *search* is generic (any degree —
the kernel machinery doesn't care); the fragment check happens per trace
step at checking time. A step outside the fragment marks the trace
S1-gated (deferred to nla-11/13); Verus census goals are overwhelmingly
inside.

## 1. Module map (Z3 file → Lean module)

| Z3 file | Lean module | trust | notes |
|---|---|---|---|
| `nlsat_types.h` (atoms, literals) | `Nlsat/Types.lean` | untrusted data | `ineq_atom` = sign condition on poly products; `root_atom y ⋈ root_i(p)`; literals = signed atoms. Multivariate polys: sparse `MPoly` over ℚ, vars = `Nat` indices with the fixed elimination order |
| `nlsat_assignment.h` | `Nlsat/Types.lean` | untrusted | partial model `var → RAlg` (real algebraic = `(QPoly, Rat × Rat)` from `Kernel/Roots.lean`, plus rational fast path) |
| `nlsat_interval_set.{h,cpp}` | `Kernel/IntervalSet.lean` | untrusted | disjoint infeasible intervals with `RAlg` endpoints + justification literals; `mk_union` (justification-preserving merge), `is_full`, `pick_in_complement` |
| `nlsat_evaluator.cpp` | `Nlsat/Evaluator.lean` | untrusted | sign of atom under partial model: substitute assigned vars → univariate ℚ[x] in the top var → `signAtRoot` / rational eval; `infeasible_intervals` of an atom = root isolation of the substituted poly + sign tests between roots |
| `nlsat_explain.cpp` (classic path) | `Nlsat/Explain.lean` | untrusted | projection loop: psc chains (already in `Kernel/QPoly.lean`), `ensure_sign` assumptions, `add_cell_lits`, `mk_linear_root`, `mk_quadratic_root` (Thom), pseudo-division sign transfer. Every emitted step also records its **trace obligation** (§2) |
| `nlsat_solver.cpp` (search core) | `Nlsat/Solver.lean` | untrusted | stages per arith var (`new_stage`), levels per decision (`new_level`), watches, `process_clause` / `updt_infeasible`, `select_witness` = `pick_in_complement`, `resolve` = Boolean resolution + explain on arith conflicts. No reorder/gc/simplify heuristics in v0 (they only affect performance, not the trace language) |
| — | `Nlsat/Trace.lean` | **shared datatype** | the trace the search emits and the checker consumes (§2) |
| — | `Nlsat/Check.lean` (nla-19) | **trusted** | discharge map §3; per-step Lean proofs, no search-side trust |

Justification-tracking note: Z3's interval sets carry the *literal* that
caused each infeasible interval; conflict explanation unions these. The
port keeps that structure — it is what makes emitted lemmas minimal, and
fidelity here is what makes run-cost comparable.

## 2. Trace language

A trace is a tree of refutation steps for "assumptions Γ are infeasible
over ℝ". Emitted by the search on UNSAT (the only case tactus needs:
the goal's negation must be refuted). Shapes (DESIGN.md §L3 table,
restricted):

```
inductive TraceStep
  | leafNumeric      -- stage-1 univariate: cell sweep over ℚ-coefficient
                     --   polys; obligations are nla-09 bridge claims
                     --   (checkNoRoot/checkPosOn/checkNegOn/checkUniqueRoot)
  | thomQuadratic    -- root-atom elimination on A·y²+B·y+C: sign literals
                     --   on disc/A/p'/p per mk_quadratic_root; obligation =
                     --   S3 kit instance
  | linearRoot       -- degree-1 root atom → plain inequality (exact
                     --   mk_linear_root arithmetic); obligation = ring/linarith
  | cellBound        -- add_cell_lits bracketing around the sample at deg ≤ 2;
                     --   obligation = S3 ordering family
  | pseudoDivision   -- lc(p)^d·h = q·p + r sign transfer; obligation =
                     --   per-instance ring identity + parity case split
  | factorSplit      -- square-free/factor step; per-instance ring identity
  | intBranch        -- x ≤ ⌊v⌋ ∨ x ≥ ⌈v⌉ splits; omega leaf
  | resolution       -- Boolean resolution combining learned clauses
```

(Exact constructor payloads to be pinned during nla-12a implementation —
each carries the concrete polynomials, sign values, and sub-traces it
needs; the principle is that **every payload is data the checker can
verify by `decide` + fixed lemmas**, never "trust me" markers.)

## 3. Discharge map (checker obligations → proof machinery)

| trace step | trusted machinery | status |
|---|---|---|
| `leafNumeric` | nla-09: `check*_sound (by decide)` | **done** (2026-07-26) |
| `thomQuadratic` | S3 kit `Templates/Quadratic.lean` | this lane (nla-19a) |
| `linearRoot` | `linarith`/`nlinarith`-free direct lemmas | with S3 kit |
| `cellBound` (deg ≤ 2) | S3 ordering family | this lane (nla-19a) |
| `pseudoDivision` | `ring` per instance + sign parity lemmas | nla-19b |
| `factorSplit` | `ring` per instance | nla-19b |
| `intBranch` | `omega` | free |
| `resolution` | propositional glue (`tauto`-shape, explicit) | nla-19b |
| any step outside deg ≤ 2 | S1 (nla-11) | out of scope, trace marked S1-gated |

## 4. Slices

- **nla-12a** `Nlsat/Types.lean` + `Nlsat/Trace.lean`: MPoly (sparse,
  ℚ coefficients, Nat vars), atoms/literals/clauses, RAlg assignment,
  trace datatypes. Plus `Kernel/IntervalSet.lean` univariate core
  (endpoints, union with justifications, pick_in_complement) — testable
  standalone against hand cases.
- **nla-12b** `Nlsat/Evaluator.lean`: atom sign + infeasible intervals
  under partial model (substitution to univariate + Roots.lean). #guard
  suite against known algebraic cases (√2, golden ratio, etc.).
- **nla-12c** `Nlsat/Solver.lean`: the search loop (stages/levels,
  watches, decide, propagate via interval sets, select_witness). SAT mode
  first (models found and *verified by evaluation* — cheap correctness
  signal), then conflict path.
- **nla-12d** `Nlsat/Explain.lean`: classic projection restricted to the
  fragment: psc-chain steps, ensure_sign bookkeeping, mk_linear_root /
  mk_quadratic_root, add_cell_lits; emits trace steps. Fragment check
  (deg ≤ 2 per top var) enforced here in v0 — out-of-fragment
  explanations abort the trace (search may still be useful as a
  disprover/model-finder).
- **nla-19a** S3 kit (`Templates/Quadratic.lean`, trusted, this session)
  + `Nlsat/Check.lean` v0: discharge leafNumeric + thomQuadratic +
  linearRoot + cellBound.
- **nla-19b** full checker: pseudoDivision/factorSplit/resolution glue;
  end-to-end: search a census-shaped goal → trace → checked theorem.
  `ordering_139` (the L1-open census specimen, degree-3 cross products)
  is the standing target *if* its trace stays in fragment; else the
  first fully-quadratic census row.
- **nla-12e** (after 19b) integer branching + Int frontend relaxation.

## 4b. Evaluator anum arithmetic (nla-12b; decision 2026-07-26)

**Danielle's call: port Z3's actual shape — similarity is not compromised
even where the mechanism doesn't affect emitted lemmas.** (This extends
the source-fidelity directive to sign-evaluation strategy.) The
resultant-only alternative was considered and rejected.

The evaluator consumes exactly three anum entry points
(`nlsat_evaluator.cpp:386,427,446,471`):
`eval_sign_at(p, x2v)`, `isolate_roots(p, undef_var_assignment(x2v, x),
roots[, signs])`, and `compare` (mini-anum, done). Z3's shapes, from
`algebraic_numbers.cpp`:

**`eval_sign_at` (:2246):**
1. *Optimistic pass*: if all assigned values are rational, evaluate in ℚ.
2. Substitute the rational fragment → `p′`; zero/const shortcuts.
3. *Interval pass*: evaluate `p′` over the algebraic cells' isolating
   intervals; refine cells (magnitude-gated) while the enclosure
   contains zero; restart if a cell normalizes to rational.
4. *Exact zero test via resultants*: `R(y) = Res_{x_i…}(y − p′, q_i(x_i))`
   over each algebraic var's defining poly `q_i`; `L = 2^{−k}` from
   `nonzero_root_lower_bound(R)`; refine until the enclosure excludes
   zero (sign known) or fits in `(−L, L)` (value is exactly zero).

**`isolate_roots` under partial assignment (:2547):** zero/const/
univariate shortcuts → substitute rationals → resultant-eliminate each
algebraic variable with its defining poly → univariate `q` whose roots
⊇ the true roots → isolate (kernel) → **filter** candidates `r` by
`eval_sign_at(p, x2v ∪ {x→r}) = 0`. Degenerate `q ≡ 0` fallbacks: linear
coefficient solve; else the auxiliary-variable (`z·x^i + …`) nested
path. **Signs variant (:2902):** refine roots to `DEFAULT_PRECISION`,
then `eval_sign_at` at `int_lt`/`select`/`int_gt` sample points between
consecutive roots.

**Key porting simplification (checked against both call sites): every
resultant elimination has a univariate rational-coefficient second
argument** (defining polys of algebraic cells). So the only multivariate
resultant needed is `Res_x(f, q)` with `q ∈ ℚ[x]`: computed as
`lc(q)^{deg_x f} · det(mult-by-(f mod q̂) on ℚ(...)[x]/(q̂))` with `q̂`
monic — a `deg q × deg q` determinant with MPoly entries by cofactor
expansion (deg 2 dominant in the fragment).

Declared divergences: **the three originally listed here (Rat-not-mpbq
endpoints, no refine rationality discovery, width-not-magnitude gating)
were all ELIMINATED by the nla-26 fidelity arc (2026-07-26)** — dyadic
`Mpbq`/`MpbqI` endpoints everywhere, `refine_core`-faithful
midpoint-zero-first refinement with became-basic re-dispatch, and
binary `lt_1div2k` magnitude/precision gating are now the shipped
shapes. The live remaining divergence list is in BOARD.md (nla-26
closing note): Sturm-vs-Descartes isolation, the ℚ[x] QPoly kernel
bridged at `ofQPoly`, root-represented rationals at shared endpoints,
and no factorization (= `factor=false` parity, → nla-27).

Slice split: **12b-i** foundations (RatInterval arithmetic, MPoly
interval evaluation, `resultantElim`, `nonzeroRootLowerBound`, RAlg
accessors) — landed with this decision; **12b-ii** `evalSignAt` +
`isolateRootsAt` assembly + the `q ≡ 0` fallback paths + evaluator
`sign_table` + `infeasible_intervals`.

## 5. Risks / notes

- **Trace payload design drift**: pin payloads only when the checker side
  consumes them (12a is written against 19a in the same arc wherever
  possible).
- **anum parity**: Z3's `anum` normalizes to rational when possible;
  our RAlg must too (`pick_in_complement` prefers rational witnesses —
  keep Z3's preference order so traces match).
- **interval_set justification semantics**: Z3 keeps *one* justification
  literal per interval and unions lazily; conflict minimality depends on
  it. Port the exact merge rules (nlsat_interval_set.cpp:mk_union cases).
- **Degenerate quadratics** (`A` sign-zero at the sample): Z3 falls to
  `mk_plinear_root` with an `ensure_sign` assumption on the linear
  coefficient — mirror exactly (nlsat_explain.cpp:854-869, 886-919).
