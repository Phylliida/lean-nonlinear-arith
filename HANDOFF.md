# HANDOFF — 2026-08-01 (12d.6a close: explain OPERATIONAL; 12d.6b ⇄ 19a arc opens)

Read first: `DESIGN-endgame.md` (the master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` (execution units; the **nla-12d** entry
has the full slice log), then `WRITEUP.md` (the explain-port
narrative: architecture, decisions, quirks, catches). Memory file
`verus-cad/memory/project_tactus_nonlinear_port.md` has the session
history. Build: Nix `lake` on PATH (not elan); `lake build` green
(7600 jobs) at commit `1e2ff57`.

## Where we are

Critical path `28 → 27 → 12b-ii → 29 → 32 → 12c → 12d.0–12d.6a` is
DONE. **The projection engine is ported and operational**: z3's
`nlsat_explain.cpp` @ 4.12.5 in full — the operator() pipeline
(process/process2/normalize/simplify/main/project), elim_vanishing,
the psc-chain engine, cell machinery, root-atom creation (linear /
quadratic-Thom / generic), the pseudo-division simplify cluster, and
the multivariate factor_core behind it (iccp + Yun + full `mod_gcd`
with Zp evaluation, Newton/sparse interpolation, skeletons, CRA).
`Explain.explain : ExplainFn` is the production explain behind the
solver's boundary; `mockExplain` stays as the test mock for boolean +
stage-0 conflicts.

**Acceptance evidence:** `x² + y² < 0` refuted end-to-end by the real
projection (zero assumption at `x := 0`, cell bounds at `x := ±1`,
stage-0 core conflict ⇒ UNSAT); multivariate SAT green; all 12c pins
re-green; ~150 new pins this arc; build 7600 jobs, sorry-free.
Trusted layer unchanged (all new code is untrusted search-side).

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>`, never the working tree.**

## Next: 12d.6b ⇄ 19a — Trace emission + Checker v0 (one arc, 2–3 sessions)

These are one arc (standing rule 3: trace payloads pin only when the
checker consumes them). BOARD.md has the 12d.6b + 19a entries.

**12d.6b — `Nlsat/Trace.lean` + emission.** The 8-shape language
(DESIGN-nlsat-quadratic §2):

```
leafNumeric | thomQuadratic | linearRoot | cellBound |
pseudoDivision | factorSplit | intBranch | resolution
```

- **Emission points** (map trace steps to explain's mechanism):
  `ensure_sign`/`add_simple_assumption` → cellBound-adjacent sign
  facts; `mk_linear_root*` → linearRoot; `mk_quadratic_root` →
  thomQuadratic; `add_cell_lits` → cellBound; `simplifyLit`'s
  pseudo-division → pseudoDivision; `add_zero_assumption` /
  `add_factors` factoring → factorSplit; stage-1 univariate leaves →
  leafNumeric; the solver's resolve → resolution.
- **Fragment gate (DECIDED, registered):** NOT an explain-side abort.
  z3's projection is degree-generic; the gate marks trace steps where
  the top-variable degree exceeds 2 (concretely: the generic
  root-atom fallback in `add_root_literal`) as **S1-gated**. The
  search stays z3-faithful; gated traces are deferred to the S1 path
  (nla-11/13).
- **Trace egress design question (pins HERE, first task):** how the
  trace leaves `SolverM` — (a) a `trace : Array TraceStep` field on
  the solver state that explain/solver append to, vs (b) `ExplainFn`
  returning `(literals × steps)`. (a) matches z3's "explain emits
  into shared state" shape and carries solver-side resolution steps
  without plumbing; (b) is more explicit but forces the signature
  change through `resolve`. Pick (a) unless a reason emerges; record
  in the 19a board entry.
- **Checker theorem shape (pins with 19a):** per-step discharge
  lemmas composing into "the learned clause is implied" — v0 keeps
  the four checkable shapes; pseudoDivision/factorSplit/resolution
  steps are marked and discharged in 19b.

**19a — `Nlsat/Check.lean` v0 (TRUSTED layer: no
assume/admit/external_body).** Discharge map:

| trace step | trusted machinery | where |
|---|---|---|
| `leafNumeric` | `checkNoRoot_sound` / `checkUniqueRoot_sound` / `checkPosOn_sound` / `checkNegOn_sound (by decide)` | `Certificates/Sound.lean:286/313/376/393` |
| `thomQuadratic` | S3 kit (12 lemmas: `quad_key`, sign-dictionary iffs both lead signs, definite-disc cases) | `Templates/Quadratic.lean` |
| `linearRoot` | plain inequality lemmas (the exact mk_linear_root arithmetic incl. LE/GE remap) | new, same style |
| `cellBound` | S3 ordering family (`quad_{left,right}_of_{inside,root}` + `quad_roots_order`) + linarith glue | `Templates/Quadratic.lean:137-199` |

**Q1 (grammar-first, prove-over-empiricism):** the emission grammar
is ALREADY enumerated from source (BOARD nla-19a: ineq shapes A1–A5,
root tiers B, cell literals C with 1-based indices and openness).
Formalize that grammar in Lean and prove the S3-coverage lemma
against it; if the grammar exceeds the current S3 family, extend the
family first (same Templates/Quadratic style).

**Acceptance (arc):** end-to-end on hand goals with algebraic cells
(√2-grade), negative probes (corrupted trace rejected), the first
search→trace→checked-theorem round trip, 12c/12d pins re-green.

**After this arc:** 19b (full checker glue — pseudoDivision/
factorSplit/resolution → **M3**; `ordering_139` is the standing
target if its trace stays in fragment), 12e (integer branching — the
search_check B&B seam is marked), 14 (the `nonlinear_arith` tactic,
`withLayerHeartbeats` budgets), 15 (tactus wiring — ½ session), 16
(parity harness, zero Z3-closes-we-don't).
Parallel lanes: S1 (11a ∥ 11c, Q7 open — 11a doubles as
resultantElim's semantic proof), L1 hardening (21/22/07b/06), nla-30
(deferred resultant generality), **nla-31 (termination proofs —
`refineNzBound` elementary, do first; the MPolyOps/MPolyGcd/
MPolyFactor partials are registered).**

## Key architecture (don't re-derive)

- **ExplainM** (`Nlsat/Explain.lean`): `StateT ExplainState SolverM`;
  per-call state = z3's per-call scratch (result, dedup, todo);
  solver-owned = `ExplainCache` (pscChains/factors memos) + flags.
  `liftS` lifts `SolverM` into `ExplainM`. Production entry:
  `Explain.explain : ExplainFn := fun lits => (operator lits).run {}`.
- **NumMode** (`Nlsat/MPolyOps.lean`): `Option ZpCtx` = z3's mpzzp
  mode flag; numeral-touching ops take `mode := none` defaults.
  `managerNormalize`: Zp balanced / **ℤ content-strip** (both live).
- **Canonical MPoly ⇒ `mk_unique = identity`**; memo tables are
  structural scans (atom-table idiom).
- **Clause polarity (load-bearing):** explain's output is a theory-
  lemma CLAUSE — every assumption appears NEGATED
  (`add_simple_assumption` emits `⟨b, !sign⟩`); the exception is
  `mk_linear_root`, which folds negation into the kind/lsign remap.
- **Const-poison = concrete `UINT_MAX`** (4294967295) in max_var
  computations (z3's release semantics; SASSERTs are debug-only).
- **CellStore** (`Kernel/CellStore.lean`): ids dangle outside their
  store; build scenarios in ONE computation; `fresh` in the
  `let n := (← get).size; modify (·.push c); return n` form.
- **Solver** (`Nlsat/Solver.lean`): `Solver.empty` (`{}`), never
  `default` (the derived `Inhabited` ignores field defaults);
  `Clause.deleted` exists (del_clause port — skip-deleted at
  canReorder/collectVarInfo/reattach).

## Standing directives (Danielle)

1. Do things the right way first; prove over empiricism; follow z3 as
   closely as possible — every divergence is bad unless signed off
   (register in DESIGN-endgame §6).
2. **"Nearly unreachable" still needs fixing** — docstrings are never
   a fallback: behavior identical in practice. Cover all cases.
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
- **where-defs capture the parent's BINDERS, not let-bound locals** —
  pass those as explicit params (the factorCore x-param trap).
  `partial` propagates to where-defs.
- **`partial` needs `Inhabited` on the return type** (`deriving
  Inhabited`); an `inductive` can't mix into a `mutual` def block.
- Dot-notation helper defs must live in the TYPE's namespace
  (`IneqKind.flip`, `RootKind.toIneqSign` moved to Types.lean).
- `Nat.log`/`Nat.log2` are not available here — local `floorLog2`
  (kernel is mathlib-free; mathlib's `!![` notation breaks
  `x[i]![j]!` downstream — keep it out of Kernel/Nlsat).
- `Array.swap!`/`Array.mergeSort` don't exist — manual set!-swap,
  `Array.qsort`, `List.mergeSort`.
- **`ZpCtx.submul` arg order**: `(a,b,out) = out − a·b` vs z3's
  `(a,b,c,out) = a − b·c` — check at every call site.
- **Never emit zero-exponent monomials `[(x, 0)]`** — use `ofVarPow`
  (two hangs from this).
- **`lc` is at the poly's OWN degree** — defective subresultant
  chains have `deg S_{d−1} < d−1` (out-of-bounds → panic-default →
  div-by-zero loop).
- Structure update is `{ si with ... }`, not `{ si.sk with ... }`;
  anonymous `⟨…⟩` ctors ignore field defaults — give all fields.
- `from` is reserved; same-named `let rec` in different branches of
  one def collide; do-notation `return` needs the value on its own
  line; `Array.back` needs a nonempty proof — `back!`.
- omega only sees literal `Nat`/`Int`-headed comparisons (Nat-binder
  helper lemmas); verify lemma names and import scope before typing;
  probe `.induct` shapes before writing case lists; `command grep`
  on this box; check `uptime` before trusting timings.
- #guard evaluates `partial` defs fine — but a looping one hangs the
  build: probe suspicious computations with standalone `#eval` files
  first (the psc hang was isolated this way).
