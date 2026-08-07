# HANDOFF — 2026-08-06 (12d.6b⇄19a: F2 skeleton + dump analysis + renameVars fix DONE; step-fact collection next, recipe below)

Read first: `DESIGN-endgame.md` (master plan — §0 finish line, §2
critical path, §6 decisions + divergence register, §8 standing
directives), then `BOARD.md` (execution units; **the nla-19a entry has
the F1–F5 and R1–R9 decisions, design review 3 (V1–V6/R1'–R4'),
design review 4 (R-i–R-viii, Danielle-approved), the F2-skeleton
entry, and the F2 dump analysis**), then `WRITEUP.md` (explain-port
narrative). Memory file `verus-cad/memory/project_tactus_nonlinear_port.md`
has the session history. Build: Nix `lake` on PATH (not elan);
`lake build` green (7608 jobs) at commit `f32047c`.

**Source-of-truth rule (unchanged): all ports cite
`git show z3-4.12.5:<path>`, never the working tree.**

## Where we are

The **12d.6b ⇄ 19a arc** (trace emission + checker v0) has landed the
trace layer, the trusted discharges, the Q1 coverage theorems, the
F0/F1/F3-engine (`Assemble.lean`), **and the F2 skeleton**: the
`nlsat_arith_valid` elaborator (`Nlsat/Refute.lean`, untrusted meta
producing kernel-checked terms) closes all four arith lemmas of the
x0²+x1²<0 refutation and soundly rejects an invalid clause
(`RefuteTests.lean`, incl. a `#guard_msgs (drop error)` probe).
Remaining in the arc: **step-fact collection into the elaborator
(bundle 6 then bundle 7 of the acceptance dump) → F3 DAG walk → F4
acceptance → F5 housekeeping** — then 19b (pseudoDivision/factorSplit
identities), 12e, 14, 15, 16.

### New since the last HANDOFF

- **renameVars z3-fidelity bug FIXED** (found by F2 groundwork):
  `MPoly.renameVars` sorted renamed terms ASCENDING by lexCompare; z3's
  manager invariant is strictly DESCENDING
  (`SASSERT(lex_compare(m_ms[i], m_ms[i+1]) > 0)` at polynomial.cpp:1457),
  matching `MPoly.add` and the checker's `MPoly.Canon`. Post-reorder
  snapshots mixed ascending input polys with descending search-created
  ones — `Canon` would have failed on renamed input polys at F2
  consumption. One-comparator fix (`.lt` → `.gt`) + regression pin in
  SolverTests; all 12c/12d pins re-green (none exercised multi-term
  renames). Commit `848d603`.
- **Acceptance driver identified + verified** (BOARD's F2 dump
  analysis): the plain √2 goal refutes at stage 0 (`leafNumeric` only).
  The real driver is the 2-var goal
  **`x0²+x1² ≥ 2 ∧ x0 ≤ 1 ∧ x1 < 1 ∧ x0 > 0 ∧ x1 > 0`**: its refutation
  exercises linearRoot, thomQuadratic (both roots of x0²−2), cellBound,
  factorSplit, and leafNumeric finals. Full consistency verified
  against z3's `R_propagate`/cover construction (dump recipe in BOARD).
- **Design review 4 recorded** (BOARD): R-i glue = linarith-first/
  nlinarith-backup with per-shape composition lemmas as fallback;
  R-ii decoder reconstructs polys via the explain-side expressions;
  R-iii root-order fact injection per (y,p) group; R-iv step-to-marker
  accumulation rule; R-v kernel cost is per-bundle-local; R-vi F-output
  contract for nla-14 (internal-order atom table); R-vii 12e flush
  discipline; R-viii the parity statement for the F assembly.

## Next: step-fact collection into `nlsat_arith_valid`

Current elaborator (Refute.lean): byContradiction → per-literal
`¬ litSatI I l` → `holds_single_*` collapses → evalP/evalM simp-unfold
→ `sq_nonneg` hints → linarith/nlinarith. The acceptance dump's
bundles need **step-derived facts** added to that frame. Work bundle 6
first (linearRoot + cellBound), then bundle 7 (thomQuadratic).

### The acceptance dump data (verbatim, post-renameVars-fix)

Atoms (internal order): 0:none, 1:`lt [x0²+x1²−2]` poly
`[(1,[(1,2)]),(1,[(0,2)]),(-2,[])]`, 2:`gt [x0−1]` `[(1,[(0,1)]),(-1,[])]`,
3:`lt [x1−1]` `[(1,[(1,1)]),(-1,[])]`, 4:`gt [x0]` `[(1,[(0,1)])]`,
5:`gt [x1]` `[(1,[(1,1)])]`, 6:`gt [x0+1]` `[(1,[(0,1)]),(1,[])]`,
7:`lt [x0−1]`, 8:`eq [x0−1]`, 9:`lt [x0²−2]` `[(1,[(0,2)]),(-2,[])]`.

- **Bundle 6** (learned `[⟨6,true⟩,⟨7,true⟩]`): steps = resolution
  (clause 1), factorSplit ×3, linearRoot(gt, y=0, `[(1,[(0,1)]),(1,[])]`,
  mkNeg=false, lcFact=none), cellBound(lower, gt, 0, 1, same),
  linearRoot(lt, y=0, `[(1,[(0,1)]),(-1,[])]`, false, none),
  cellBound(upper, lt, 0, 1, same), arith(
  core=`[⟨5,false⟩,⟨1,true⟩,⟨3,false⟩]`,
  proj=`[⟨6,true⟩,⟨7,true⟩]`), clause 5, clause 3.
  Arith clause: `¬(x0+1>0) ∨ ¬(x0−1<0) ∨ (x1>0) ∨ (x0²+x1²≥2) ∨ (x1≥1)`.
- **Bundle 7** (learned `[⟨4,true⟩,⟨8,true⟩,⟨9,true⟩]`): steps =
  resolution (clause 1), factorSplit ×3, thomQuadratic(gt, 0, 1,
  `[(1,[(0,2)]),(-2,[])]`, sq=1, sa=1, spd=1, sp=−1), cellBound(lower,
  gt, 0, 1, same), thomQuadratic(lt, 0, 2, same, 1, 1, 1, −1),
  cellBound(upper, lt, 0, 2, same), arith(core as bundle 6,
  proj=`[⟨8,true⟩,⟨4,true⟩,⟨9,true⟩]`), clause 5, clause 3.
  Arith clause: `¬(x0=1) ∨ ¬(x0>0) ∨ ¬(x0²−2<0) ∨ (x1>0) ∨
  (x0²+x1²≥2) ∨ (x1≥1)`.
- **Final bundle**: three leafNumeric markers, arith cores
  `[⟨7,true⟩,⟨9,true⟩,⟨2,true⟩]`, `[⟨7,true⟩,⟨8,true⟩,⟨2,true⟩]`,
  `[⟨4,false⟩,⟨6,true⟩]` — all trivially valid.

### Recipe (bundle 6 = linearRoot + cellBound first)

The literal-failure facts alone do NOT close these arith clauses (the
proj literals' facts are sample-cell facts; the root comparisons are
load-bearing). Add per-step fact collection:

1. **linearRoot step** → `coverage_linearRoot ρ k y i p mkNeg lcFact
   hgram hcan hlc : ¬ SHolds ρ (linearRootEmitted k p mkNeg).1
   (emitted).2 ↔ rootCmp k (ρ y) (rootVal ρ y i p)`.
   - `hgram` (Grammar witness): elaborator-assembled constructor app;
     conditions are rfl/decide-grade on literal polys (degreeIn
     equalities, sign ranges, coeffsIn facts — coeffsIn kernel-reduces
     when every degree class is a singleton, true here).
   - `hcan` (MPoly.Canon): NO Decidable instance — assemble in meta:
     Pairwise via List lemmas with rfl-grade cmp facts
     (`Monomial.cmp`/`lexCompare` DO kernel-reduce; only the mul family
     is WF-stuck) + per-term decides (pLin_canon pattern in
     CheckTests).
   - `hlc`: vacuous/const here (lcFact=none with const lc — the
     `linearRoot_hAq` derivation handles it from the grammar's mkNeg
     folds).
   - The emitted literal (`linearRootEmitted`, Check.lean:432 — the
     kind/neg remap) is matched BY VALUE against a proj literal's atom;
     its failure + the iff's `.mp` gives the rootCmp fact. rootCmp with
     concrete k unfolds to the ℝ comparison; `rootVal` stays opaque.
2. **cellBound step** → `cellBound_generic ρ k y i p hfails` (the
   negated root atom failing gives count + rootCmp) — but note: in
   this dump the cellBound literals ARE the Thom/linear-encoded sign
   literals (deg ≤ 2 — no root atoms in the table); the plinear/
   degenerate pairing (`cellBound_plinear`) and coefficient links only
   bite in the sa=0 degenerate case, not here. For bundle 6 the
   cellBound step's fact is the SAME rootCmp the paired linearRoot
   already gives (R5 redundancy — collecting both is fine).
3. **factorSplit steps: skip (R6)** — their zero-assumption literal
   (bundle 7's `⟨8,true⟩` = ¬(x0−1=0)) yields its fact directly from
   the atom via the holds_single_eq collapse; the factorization
   identity is never needed (semantics is ∃-over-factors).
4. **pseudoDivision/intBranch anywhere ⇒ reject** (R7/F0 isV0).
5. **R-iii injection:** group rootVal occurrences by (y,p); ≥2 indices
   in one arith clause ⇒ add `quad_roots_order`/`quadRoot_le` facts.
   Bundle 7 needs it (roots 1 and 2 of x0²−2).
6. Glue unchanged (linarith first). The expected bundle-7 close:
   sign-case evaluation of `thomFormula` from the spd/sp facts (see
   below) + order facts + linarith.

### Recipe (bundle 7 = thomQuadratic — the expected hard part)

`coverage_thomQuadratic ρ k y i p sq sa spd sp hgram hcan hAm hdm :
rootCmp k (ρ y) (rootVal ρ y i p) ↔ thomFormula k i
  (leadSgn A_val * evalP ρ p) (leadSgn A_val * (2*A_val*ρ y + B_val))`.

- `hAm`/`hdm` (signMatches of A and disc): A and disc are CONST polys
  here (A=1, disc=8) — signMatches by decide/Int-cast lemmas, no proj
  literal needed (const signs are decidable per the grammar's E1
  forms). When non-const, source from the corresponding proj sign
  literal failing (V-ii bridges: failing negated sign literal →
  `IneqAtom.Holds` → holds_single_* → signMatches).
- **thomFormula evaluation (the F2 case work E2 deferred):** from the
  spd/sp sign facts evaluate the formula to a rootCmp (or its
  negation). The spd literal in the atom table is on **x0** (content-
  stripped by `managerNormalize` — z3 :803), NOT on `2·x0`: match by
  value against `managerNormalize none (2·A·y + B)` reconstructed the
  explain-side way (R-ii), bridge via `signMatches_managerNormalize`
  (Check.lean:1154) + the pDiff bridge (Check.lean:1198). sp's literal
  is on p itself (`⟨9,true⟩`).
- leadSgn weighting: A_val = 1 > 0 here, so leadSgn = 1 — the sign
  facts pass through unchanged; the general case flips signs (finite
  case split).

### F3 walk (after bundles close)

Per learned cid in increasing order: F-set = antecedent clauses (cids
from `.clause` markers — always smaller; input from Γ hypotheses,
learned from earlier fold steps) ∪ the bundle's arith clauses (F2
output); target = `bundle.lemma.toList` (assert byte-identical to
`clauses[cid].lits` by decide, V1); skip `.decision` markers. Apply
`upRefutes_sound` with the RUP check `by decide` (NEVER native_decide
in the trusted layer). Final bundle: target `[]` ⇒ False. Theorem:
`∀ ρ, (∀ input clause C, clauseHolds ρ atoms C) → False`, bridged via
`clauseSatI_interp` (per-literal decodability `∃ a, atoms[l.bvar]? =
some (some a)` by decide, reject on failure). Hand-verified on this
dump: ¬target units ⟨5,true⟩ against input clause 5 → conflict.
The dump's RUP sets are small; kernel decide cost is per-bundle-local
(R-v).

### F4 acceptance + F5

F4: the 2-var driver end-to-end (tactic closes the UNSAT goal from the
snapshot); factorSplit-bearing trace x²+2x+1 (may pull the 19b
identity forward, accepted risk); negative probes per R4' (corrupted
mkNeg, corrupted sp — parse-level rejections via the E1 grammar
tightenings); all 12c/12d pins re-green. F5 (R8 + R1'): split
Check.lean into Semantics/Discharge; unify discharge hypotheses on
full `MPoly.Canon`; normalize `↑0`-form hypotheses to `(0 : ℝ)`.

**After this arc:** 19b (identities → M3; `ordering_139` standing
target if its trace stays in fragment), 12e (integer branching), 14
(the `nonlinear_arith` tactic, `withLayerHeartbeats`), 15 (tactus
wiring, ½ session), 16 (parity harness).

## Traps / lessons (new this arc — also in BOARD/memory)

- **Kernel-reduction trap (load-bearing):** `Monomial.mul`, `MPoly.add`
  (and downstream `MPoly.mul`/`smulTerm`/`sub`) are WF-compiled — they
  do NOT reduce under kernel whnf/rfl/decide. `Monomial.cmp`/
  `lexCompare` DO reduce. Consequences: checker-facing polys must be
  LITERAL-LIST form (what nla-14 will quote natively anyway); `Canon`
  is meta-assembled (no Decidable instance); `coeffsIn` reduces only
  when every degree class is a singleton; WF-built decoder
  reconstructions (disc/pDiff/reduct-q) must bridge at the evalP level
  via the hom suite, never kernel decide; `upRefutes … by decide` is
  safe (Nat/Bool only).
- **Phantom-bug lesson (cost ~2h):** a misread `neg` field in a dumped
  marker literal made a valid arith clause decode as invalid and
  launched a full audit of (correct) justification polarity. When a
  decode makes z3 look unsound, re-verify the decode against the raw
  dump BEFORE auditing semantics.
- **Elaborator mechanics (F2 skeleton, each cost real time):** ALL meta
  ops typechecking terms that mention context fvars must run inside the
  CURRENT mvar's `withContext` (hFvar/noted facts leak otherwise —
  "unknown free variable"); the `List.Mem` decidable instance is keyed
  on `Membership.mem`, not raw `List.Mem`; `mkAppM` with zero args
  returns the BARE constant (∀-type uninstantiated — use `mkAppOptM`
  with the proposition, e.g. `Classical.not_not`); `Exists.intro`'s
  motive is HOU-uninferable — supply the lambda explicitly;
  `Literal` is ambiguous with `Lean.Literal` outside the Nlsat
  namespace; `Meta.evalExpr` needs properly universe-elaborated
  expected types (`Term.elabType` of a quotation, not `mkConst`);
  `#guard_msgs (drop error)` for rejection probes (exact-text matching
  is whitespace-fragile).
- **Numeral defaulting (standing until F5's R1'):** annotate `(0 : ℝ)`
  in statements; goal-directed `exact_mod_cast` for cast-zero hyps;
  `Int.cast_lt_zero.mpr`/`Int.cast_pos.mpr` to produce cast facts.
- `if (b : Bool)` reduction: `if_pos rfl`/`if_neg Bool.false_ne_true`,
  not if_true/if_false.
