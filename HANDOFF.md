# HANDOFF — 2026-07-31 (post nla-12c close + design review; 12d arc opens)

Read first: `DESIGN-endgame.md` (the master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` (execution units; **nla-12c** entry has
the solver design-review log + 12d carry-overs). Memory file
`verus-cad/memory/project_tactus_nonlinear_port.md` has the session
history. Build: Nix `lake` on PATH (not elan); `lake build` green
(7590 jobs) at commit `6b4b43f`.

## Where we are

Critical path `28 → 27 → 12b-ii → 29 → 32 → 12c` is DONE. L1
saturation, the computational kernel (QPoly/Mpbq/BivPoly/RAlg/Factor/
Roots/CellStore/AnumArith), the nlsat evaluator lane (Types,
IntervalSet, AnumEval, Evaluator + q≡0 fallbacks, EvaluatorTable), the
4.12.5 re-anchoring audit (nla-32), and **the solver loop (nla-12c,
all six slices + design review)** are landed, pinned, sorry-free.
Trusted layer unchanged (all new code is untrusted search-side).

`Nlsat/Solver.lean` ports `nlsat_solver.cpp`@4.12.5: hash-consed atom
table, trail/undo family (quirks verbatim), propagation with
justification capture, search (SAT models verified by evaluation),
full resolve with the **`ExplainFn` boundary**, reorder + check shell.
The solver runs end-to-end today: SAT/UNSAT answers with mockExplain
(faithful for boolean + stage-0 conflicts). What's missing for real
multivariate UNSAT is exactly 12d: the projection that produces
previous-stage literals from an arith conflict core.

**Source-of-truth rule (nla-32): all ports cite
`git show z3-4.12.5:<path>`, never the working tree** (the checkout
is 4.16-nightly and differs materially).

## Next: nla-12d + nla-19a — Explain + Checker v0 (one arc, 3–4 sessions)

**BOARDED 2026-08-01** — full slice specs (12d.1–12d.6 + 19a) with the
interface-audit findings, non-port register, and quirk list are in
BOARD.md (`nla-12d`, `nla-19a` entries).

These are deliberately one arc (DESIGN-endgame §2.4): trace payloads
pin only when the checker consumes them (standing rule 3).

**Source:** `git show z3-4.12.5:src/nlsat/nlsat_explain.{h,cpp}`
(1914 lines; levelwise does not exist at 4.12.5 — the classic
Jovanović–de Moura projection is the WHOLE file).
**Re-anchored entry points** (the DESIGN-nlsat-quadratic line numbers
came from HEAD; these are 4.12.5):

- `operator()` :1486 — the entry the solver calls (resets m_ps,
  collects literal polys, per-stage projection loop at :1381).
- `project(var x, …)` :1503 → `project(ps, max_x)` :990 — dispatch:
  `add_cell_lits` :1000 / `add_lc` :1008 + root-atom creation.
- `elim_vanishing` :307/:363/:380/:488 — vanishing leading-coefficient
  elimination (with assumptions when a factor is lower-stage).
- `ensure_sign` :822, `add_assumption` :294, `add_zero_assumption` :262.
- `add_cell_lits` :899, `add_lc` :610.
- Root-atom creation: `mk_linear_root` :742/:861, `mk_plinear_root`
  :756 (degenerate-A fallback with its ensure_sign assumption),
  `mk_quadratic_root` :787 (Thom encoding — the S3 one-identity).
- Pseudo-division sign transfer: :1037–:1259 (`pseudo_remainder`
  :1127, `add_lc_ineq`/`add_lc_diseq` :1085).
- `m_cache.factor` :225, `m_cache.psc_chain` :235 (factor=true parity
  via nla-27's Factor; psc chains via QPoly).
- Public interface (nlsat_explain.h): `reset`, `set_simplify_cores`
  (true), `set_minimize_cores` (false), `set_full_dimensional`
  (solver's check() computes it — flag already stored),
  `set_factor` (true), `set_signed_project`, `maximize`,
  `test_root_literal`. **Interface audit DONE (2026-08-01):** the nra
  path touches only the flags + `operator()` + `reset`
  (nlsat_solver.cpp:239/:276-278/:1611/:1828; nra_solver.cpp never
  calls explain). Non-ports registered in BOARD.md nla-12d: minimize
  cluster, signed_project cluster, maximize (dead+buggy upstream),
  public project(var,…), keep_p_x, test_root_literal. **The
  pseudo-division simplify cluster is LIVE** (simplify_cores=true is
  the nra default — not a flag case).

**The ExplainFn contract (already live):**
`Solver.lean` defines `ExplainFn := Array Literal → SolverM (Option
(Array Literal))` — given the conflict core, return the projection
literals to prepend; `resolve_lazy_justification` appends the negated
core itself (z3's `m_explain(jst.lits, out)` + push-back-~core shape).
12d delivers the real projection behind this signature; `mockExplain`
(`pure (some #[])`) stays as the test mock.

**Fragment gate:** every projection/root step stays at **degree ≤ 2
in the top variable**, checked at explain time; out-of-fragment marks
the trace S1-gated (search remains a model-finder/disprover). The
one-identity insight (`4a·p = (2ay+b)² − disc`) is why deg ≤ 2 is
S1-free (DESIGN-nlsat-quadratic §0).

**Trace:** `Nlsat/Trace.lean` lands here — the 8-shape language
(leafNumeric / thomQuadratic / linearRoot / cellBound /
pseudoDivision / factorSplit / intBranch / resolution;
DESIGN-nlsat-quadratic §2). Payloads pin against the checker (19a),
never before.

**19a — `Nlsat/Check.lean` v0 (trusted):** discharge map —
`leafNumeric` → nla-09 certificates (`check*_sound (by decide)`);
`thomQuadratic` → S3 kit (`Templates/Quadratic.lean`);
`linearRoot` → plain inequality lemmas; `cellBound` → the S3 4-lemma
ordering family + linarith glue. **Q1 (grammar-first):** derive the
cell-shape grammar from `nlsat_explain.cpp` source (what
add_cell_lits + the three mk_*_root can emit: root-atom kinds ×
openness × sample position) and prove the S3-coverage lemma against
it during 19a; extend the S3 family first if the grammar exceeds it.

**Slice outline (board it at arc open):** 12d.1 re-anchor + scaffold
(explain state: todo_set + `m_cache` port — mk_unique/psc_chain/
factor wrappers; assumption/ensure_sign machinery; flags) → 12d.2
elim_vanishing → 12d.3 cell machinery (sample, add_cell_lits,
add_lc) → 12d.4 root-atom creation (via `Solver.mkRootAtom` — dedup +
flip normalization live there now) → 12d.5 projection loop (psc
chains, pseudo-division, square-free steps) → 12d.6 operator() +
fragment gate + trace emission → 19a checker + Q1 proof.
**Acceptance (arc):** end-to-end on hand goals with algebraic cells
(√2-grade), negative probes (corrupted trace rejected), first
search→trace→checked-theorem round trip, and the 12c pins re-green
with the real explain replacing the mock on the multivariate-conflict
shapes (the mock's stage-0 pins stay).

**12d carry-overs from the 12c review (boarded):** port real
`remove_learned_roots` + the `del_clause` machinery when explain's
root atoms arrive (today it's a no-op with a parity argument);
`m_cache` (nlsat polynomial cache: mk_unique/psc_chain/factor) lands
with explain; root atoms only via `Solver.mkRootAtom`.

After this arc: 19b (full checker glue — pseudoDivision/factorSplit/
resolution; **M3**), 12e (integer branching — the search_check B&B
loop is the marked seam), 14 (nonlinear_arith tactic,
withLayerHeartbeats), 15 (tactus wiring), 16 (parity harness).
Parallel lanes: S1 (11a ∥ 11c, Q7 open — 11a doubles as
resultantElim's semantic proof), L1 hardening (21/22/07b/06), nla-30
(deferred multivariate-resultant generality), **nla-31 (termination
proofs — `refineNzBound` is elementary, do it first)**.

## Key architecture (don't re-derive)

- **CellStore** (`Kernel/CellStore.lean`): `CellStore = Array RAlg`,
  `CellM = StateM CellStore`, in-place updates; all ops that refine
  write back. Build mixed-set scenarios in ONE CellM computation (ids
  dangle outside their store). `fresh` must be the
  `let n := (← get).size; modify (·.push c); return n` form.
- **Solver** (`Nlsat/Solver.lean`): `SolverM = StateM Solver`,
  `liftC` for CellM ops. z3's `null_var` = `Option` (`optVarLt`
  replicates UINT_MAX semantics incl. poisoning). Single clause table
  + learned flag (z3's two-table iterations are filters — mapped).
  **`Solver.empty` (`{}`), never `default`** — the derived
  `Inhabited` ignores structure field defaults (the simplifyCores
  trap).
- **Anum arithmetic** (`Kernel/AnumArith.lean`): z3's field ops 1:1;
  became-basic is DATA (`MkBinaryResult`/`MkUnaryResult`); z3's
  throws are `Option` (`none` = exception image; never Lean's silent
  1/0=0, 0^0=1).
- **evalAnum / evalSignAt** (`Nlsat/Evaluator.lean`): `t_eval_core`
  verbatim; stored-cell refinements persist via the store.
- **BivPoly.resultantElimY**: approved multiplication-matrix route
  (capability-identical on every reachable input; generality →
  nla-30). `detBiv` is Bareiss; `detBivLaplace` the differential
  reference.

## Standing directives (Danielle)

1. Do things the right way first; prove over empiricism; follow z3 as
   closely as possible — every divergence is bad unless signed off
   (register in DESIGN-endgame §6).
2. **"Nearly unreachable" still needs fixing** — docstrings are never
   a fallback: behavior identical in practice. Cover all cases, not
   just expected ones.
3. Source-fidelity over equivalent-engine + empirical check: port the
   mechanism (the review method that works: re-read z3 against the
   port).
4. Parity directive: schedulers only select from the closure; every
   change states its parity argument.
5. No assume/admit/external_body in the trusted layer.
6. Budgets: `withLayerHeartbeats`, never fraction-of-remaining.
7. Implement in this window's style — no coder agents for code;
   commit freely, small commits.

## Lean traps (all recorded in memory)

- **The derived `Inhabited` ignores structure field defaults** — use
  `{}` (`Solver.empty`), never `default`.
- Same-named `let rec` in different branches of one def collide —
  name distinctly.
- `.ok (a, b)` on a multi-field constructor via anonymous dot-notation
  parses as a `Prod` — write `.ok a b`.
- `partial` needs `Inhabited` on the return type (`deriving
  Inhabited`); a dropped `let rec` tail call surfaces as
  `unexpected token '|'` at the NEXT match arm.
- mathlib ships a root-level `Dyadic` that captures unqualified name
  resolution — kernel type is `Mpbq`.
- `termination_by` + proof-carrying subtype + `decreasing_by
  all_goals (simp_wf; assumption)` works for measure walkers in `do`.
- do-notation `return` needs the value on its own line (a comment
  first breaks parsing); `List.qsort` doesn't exist — `List.mergeSort`
  (stable); `Array.back` needs a nonempty proof — `back!`.
- omega only sees literal `Nat`/`Int`-headed comparisons (25.4 lesson
  — Nat-binder helper lemmas).
- Verify lemma names and import scope before typing; probe `.induct`
  shapes before writing case lists; `command grep` on this box; check
  `uptime` before trusting timings.
