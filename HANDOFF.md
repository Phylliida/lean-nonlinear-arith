# HANDOFF — 2026-08-06 (12d.6b⇄19a: E + F0/F1/F3-engine + design review 3 DONE; F2 elaborator next, recipe below)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` (execution units; **the nla-19a entry has
the F1–F5 and R1–R9 design-review decisions, design review 3
(V1–V6/R1'–R4'), the Slice E/F sub-slice plan, and the F2-groundwork
dump analysis**), then `WRITEUP.md` (explain-port narrative). Memory
file `verus-cad/memory/project_tactus_nonlinear_port.md` has the
session history. Build: Nix `lake` on PATH (not elan); `lake build`
green (7606 jobs) at commit `772e3d1`.

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>`, never the working tree.**

## Where we are

Critical path `… → 12d.0–12d.6a` (projection engine, see previous
HANDOFF) is done; the **12d.6b ⇄ 19a arc (trace emission + checker
v0) has landed its core AND its coverage half**: the 8-shape trace
language, the egress, emission for all 8 shapes, trusted discharges +
pins for the four v0 shapes, and (2026-08-06) the finalized emission
grammar + `Nlsat/Coverage.lean` (Q1 proved: grammar + fragment ⇒ the
discharge kit applies, per constructor — see BOARD's 19a entry for the
E1 audit findings incl. the const-lcFact completeness fix, and the E2
theorem shapes). Remaining in the arc: **checker assembly +
acceptance (Slice F/G — sub-slices F0–F5 in BOARD)** — then 19b (now
just pseudoDivision/factorSplit identities → M3), 12e, 14, 15, 16.

### The trace layer (12d.6b, untrusted search-side)

- `Nlsat/Trace.lean`: 8-shape `TraceStep` (leafNumeric | thomQuadratic |
  linearRoot | cellBound | pseudoDivision | factorSplit | intBranch |
  resolution) + `rootGeneric` (B-tier fallback spelled out; the
  fragment gate is **checker-computed** — F3). `TraceBundle` per
  learned clause. Emission grammar DRAFT (inductive, per-constructor
  source refs — finalizes with Q1).
- Egress (F1): `Solver.pendingTrace` buffer (cleared at each resolve
  round reset — z3's `m_lemma` boundary), flushed into
  `traceBundles : Array (Option TraceBundle)` parallel to `clauses` at
  the two `mkClause … true` sites; `finalRefutation` at the empty-lemma
  UNSAT exit; F2 extraction seam in `check()` snapshots
  `(atoms, clauses, bundles, final)` in internal var order BEFORE
  `restoreOrder`. Resolution markers at every antecedent
  (clause / arith / decision). Append-only — all 12c/12d pins stayed
  byte-green.
- Emission points: `mkLinearRoot5` (linearRoot, `lcFact` for the
  plinear variant), `mkQuadraticRoot` (thomQuadratic with sq/sa/spd/sp
  sign payloads), `addRootLiteral` generic fallback (rootGeneric),
  `addCellLits` (cellBound after each encoding step, exact/lower/upper),
  `simplifyLit` (pseudoDivision), `addZeroAssumption` + `addFactors`
  (factorSplit), `operator()` (leafNumeric marker when the whole output
  clause is univariate-const in var 0), resolve (resolution markers).

### The checker layer (19a, TRUSTED — no sorry/admit/external_body)

`Nlsat/Check.lean` (~1400 lines): `evalM`/`evalP` semantics over ℝ +
hom suite (add/neg/sub/smulTerm/mul); checker-side `coeffsOf`
(structural mirror of `coeffsIn` — **bridge theorem proved**:
`coeffsOf_eq_coeffsIn_toList`, R3); `coeffsOf_canon`; linear/quadratic
form bridges; `IneqAtom.Holds` sign semantics (**verified = z3
`eval_ineq` exactly**); `RootAtom.Holds`/`Atom.Holds`/`ALitHolds` with
the **no-roots rule** (`rootCount`, R2); discharges per shape:
`linearRoot_discharge` (lin_root_* + `rootCmp`, LE/GE remap + negation
fold), S3 extension (`Templates/Quadratic.lean`: sqrt `quadRoot` + full
point-vs-root dictionary), `thom_iff` (master equivalence),
`thom_discharge` (leadSgn/quadRootVal flip), `cellBound_linear/thom`
wrappers, `rootGeneric_discharge`, leafNumeric stage-1 glue (v0 leaves
are trichotomy/nlinarith-grade — R4; CertGen reserved for deg ≥ 3).
`Nlsat/CheckTests.lean`: pins per slice incl. live-emission
reconstruction checks and `root₂(y²−2) = √2`.

### Design reviews (both in BOARD.md, Danielle-approved)

- **F1–F5 (2026-08-03, pre-implementation):** egress = buffer +
  per-clause bundles (NOT a flat log — resolve has multiple rounds,
  aborted rounds self-discard, UNSAT exit has no clause); extraction
  seam pre-restoreOrder; fragment gate checker-computed; grammar→S3 is
  the proved direction (explain→grammar stays source-fidelity + pins);
  emit all occurring shapes now, discharge later.
- **R1–R9 (2026-08-03, post-session-1):** R1 resolution replay is
  propositional-per-bundle (tauto-grade DAG walk, NOT z3 trail-scan)
  and comes forward into v0 — **19b shrinks to pseudoDivision/
  factorSplit identities**. R4 leafNumeric v0 = glue for all deg ≤ 2
  univariate leaves. R6 **factorSplit steps are ALWAYS safe to ignore**
  (the factored poly never appears in any clause literal — only its
  factors do — zero coverage loss). R7 pseudoDivision NOT always
  ignorable (rewrites can be load-bearing — v0 ignores the step,
  derivation may fail = sound rejection). R5 cellBound redundancy
  intentional. R8 Check.lean splits at assembly. R9 duplicate
  factorSplit steps benign.

### Live trace evidence

`x²+y²<0` refutation dumps coherently: three mid-search bundles (zero
assumption `x₀≠0`, cell bounds `x₀≥0`, `x₀≤0` — each = conflict-clause
marker + factorSplit + linearRoot + cellBound + arith marker) + final
bundle (`leafNumeric 0` + trichotomy clause `x₀<0 ∨ x₀=0 ∨ x₀>0`) →
empty clause. (Reproduce: the /tmp/dump_trace.lean recipe from the
memory file — search `search (resolve Explain.explain)` on the unit
clause, print `finalRefutation`/`traceBundles`.)

## Next: the F2 elaborator (per-bundle arith-lemma validity) — full recipe

F0/F1/F3-engine landed (Assemble.lean); design review 3 done
(V1–V6 clean, R1'/R2' approved, P-b escape hatch recorded — all in
BOARD's 19a entry). **F2 is the arc's biggest remaining piece — a
term-producing elaborator (nla-09 house style), estimated ~1 session
with iteration risk in the nlinarith glue.** Suggested home: a new
`Nlsat/Refute.lean` (meta/elaborator code is untrusted; every produced
term is kernel-checked against the trusted lemmas).

**The snapshot (input to the elaborator).** Run
`Solver.run' (do Solver.init; mkVar …; mkIneqLiteral …; mkClause …;
Solver.check (Solver.resolve Explain.explain))`; on `some .false`,
`s.refutation = some (atoms, clauses, bundles, fin)`. Meta-side
evaluation of the pure solver run (unsafe/native eval) is fine —
untrusted. Dump recipe for x0²+x1²<0 is in the BOARD entry ("F2
groundwork"); `lean --run` a scratch file, print `s.refutation`.

**Per-bundle validity (the F2 core).** For each `.arith core proj`
marker in a bundle, produce
`clauseSatI (interp ρ atoms) (arithClause core proj)` — note
`arithClause` = `proj ++ ¬core` (List forms). Pattern per marker:
1. Assume every literal of the arith clause fails; unfold
   `litSatI`/`interp`/`Atom.Holds`/`IneqAtom.Holds` to evalP-level ℝ
   facts (the `holds_single_*` collapses for single-factor atoms).
2. Collect per-step facts from the bundle's projection steps via
   Coverage.lean: `coverage_linearRoot` / `coverage_thomQuadratic`
   (give `rootCmp` iffs at `rootVal`), cellBound facts via
   `cellBound_linear` / `cellBound_thom` / `cellBound_plinear` /
   `cellBound_generic`. Grammar witnesses are elaborator-built from
   payload data (all conditions are decidable-by-construction);
   `MPoly.Canon` of payload polys by `decide`; sign facts
   (`signMatches`) come from the corresponding proj literals failing.
   factorSplit steps: skip (R6). pseudoDivision present ⇒ reject
   (R7). leafNumeric: recompute the univariate-const-in-var-0
   property from the arith clause's polys (F3), then it's
   trichotomy/nlinarith glue (R4).
3. Close `False` by nlinarith/linarith over the collected facts.
   `quadRootVal`/`rootVal` values are opaque ℝ constants to the
   solver; order facts come from `quad_roots_order`/`quadRoot_le`
   when needed. Failure anywhere = sound rejection.
CAVEAT (from the dump): x0²+x1²<0's arith lemmas are all trivially
valid — the discharge chain is only really exercised by the √2-grade
acceptance goal (shape `x0 ≥ 0 ∧ x0² ≥ 2 ∧ x0 ≤ 1`).

**The walk (F3 — engine done, this is the assembly).** Per learned
cid, in increasing order: F-set = antecedent clauses (cids from
`.clause` markers — always smaller cids; input clauses from the Γ
hypotheses, learned ones from earlier fold steps) ∪ the bundle's
arith clauses (from step 2); target = `bundle.lemma.toList`
(byte-identical to `clauses[cid].lits` — V1; assert by `decide`);
skip `.decision` markers (their literal is already in the target).
Apply `upRefutes_sound` with the RUP check discharged `by decide`
(native_decide is NOT allowed in the trusted layer; pins may use
it). Final bundle: same with target `[]` ⇒ `False`. The theorem
produced: `∀ ρ, (∀ input clause C, clauseHolds ρ atoms C) → False`,
bridged via `clauseSatI_interp` (needs per-literal decodability
`∃ a, atoms[l.bvar]? = some (some a)` — decidable checks, reject on
failure).

**F4 acceptance:** √2-grade hand goal above; a factorSplit-bearing
trace (x²+2x+1 — may pull the 19b identity forward, accepted risk);
negative probes: corrupted trace rejected — per R4' include a
corrupted-mkNeg and a corrupted-sp step (the E1 pins make those
parse-level rejections); all 12c/12d pins re-green.

**F5 (R8 + R1'):** split Check.lean into Semantics/Discharge; unify
discharge hypotheses on full `MPoly.Canon`; normalize `↑0`-form
hypotheses to `(0 : ℝ)` annotations (R1').

**After this arc:** 19b (identities → M3; `ordering_139` standing
target if its trace stays in fragment), 12e (integer branching), 14
(the `nonlinear_arith` tactic, `withLayerHeartbeats`), 15 (tactus
wiring, ½ session), 16 (parity harness).

## Traps / lessons (new this arc — also in memory file)

- **Numeral defaulting in the Nlsat namespace context (2026-08-06,
  cost ~1h):** a standalone `0` in a statement Prop position can
  elaborate as `Nat.cast 0` (OfNat defaulting beats unification when
  the term has `[1]!` subterms); the goal then shows `↑0`, which is
  NOT defeq to `(0:ℝ)` at default transparency, and linarith is blind
  to Int hypotheses. Discipline: annotate `(0 : ℝ)` in statements;
  bridge to cast-zero hypotheses with GOAL-directed `exact_mod_cast`;
  produce cast facts with `Int.cast_lt_zero.mpr`/`Int.cast_pos.mpr`,
  never `exact_mod_cast` in argument position.
- `if (b : Bool)` reduction: `if_true`/`if_false` are for `ite True`/
  `ite False` — the Bool-condition if is `ite (b = true)`; use
  `rw [h, if_pos rfl]` / `rw [h, if_neg Bool.false_ne_true]`.

- `variable (ρ)` + equation-style defs: the recursive reference needs
  explicit ρ — make ρ an explicit parameter instead.
- Var-abbrev omega rule (standing directive 8): omega sees only
  literal Nat/Int-headed comparisons — Nat-binder helper lemmas +
  explicit `Nat.*` term lemmas; record projections need a typed `have`
  before omega sees them.
- `eq_or_lt_of_le` gives `0 = x` FIRST (branch order bit me twice).
- `∀ (a, m) ∈ l` tuple binders unsupported — use atomic binders +
  obtain.
- `simp only [List.set]` doesn't fire at hypotheses — use rfl-have + rw.
- `Array.set!` IS `setIfInBounds` (matches `List.set` unconditionally);
  `(l.toArray).toList = l` is rfl; `Array.toList_inj`,
  `List.getElem!_toArray`, `Array.toList_setIfInBounds`,
  `List.toArray_replicate` exist; `List.forIn_cons` exists; use
  `Id.run_bind`/`Id.run_pure` (Id.bind_eq/pure_eq deprecated).
- `fun_induction` cases for defs with `have c := a+b` carry an EXTRA
  binder; the `let` in `MPoly.add`'s eq-branch gets inlined in goals —
  match `a + b`, not `c`.
- `set` can introduce `↑0`/`↑4` casts in folded hypotheses — sidestep
  with a named def (leadSgn precedent) or exact_mod_cast.
- `rw`'s trailing rfl is reducible-only — close match-def iffs with
  `exact Iff.rfl`.
- For `for`-loop↔foldl bridges: one simulation lemma
  (`forIn_coeffs` pattern) + `List.forIn_cons` + Id-run simp set.
- `Int.gcd` returns Nat (coerce); `Int.gcd_dvd_left/right`,
  `Int.natCast_nonneg`, `eq_zero_of_zero_dvd` for the ic lemmas.
