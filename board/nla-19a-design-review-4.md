## nla-19a design review 4 `done` (2026-08-06, pre-F2; R-i–R-viii Danielle-approved same day)

Method: adversarial trace of the F2 recipe (HANDOFF + F2-groundwork
block above) against `git show z3-4.12.5:src/nlsat/{nlsat_solver,
nlsat_explain}.cpp` and the trusted layer (Check/Coverage/Assemble/
Trace/Explain), pre-implementation, two lenses: right-way (trust
shape) and z3 parity. Danielle's framing: faithful to z3 as long as
ALL cases are covered, no matter how rare.

**VERIFIED CLEAN:**
- **V-i (arith lemma shape verbatim):** z3 `resolve_lazy_justification`
  (:1827-1829: `m_explain(...)` then `push_back(~jst.lit(i))`) =
  port's `lazyClause := proj; push l.negate` (Solver.lean:918-920) =
  `arithClause core proj = proj ++ ¬core` (Assemble.lean:89). The
  `.arith` marker payload records exactly (core, proj). Trail-side
  details (z3's DEBUG_CODE b-var literal) are assignment-level, not
  validity-level — irrelevant to the checker.
- **V-ii (sign-literal → signMatches bridge by construction):** z3
  `add_simple_assumption` (:287-291) emits `literal l(b, !sign)` = the
  NEGATED single-factor atom, kind from the sample sign; port
  identical (Explain.lean:194-197/:209-213). A proj sign literal
  FAILING yields `IneqAtom.Holds` of the sign atom directly →
  `holds_single_lt/gt/eq` (Check.lean:413-424) → the `signMatches`
  hypotheses (hlc/hAm/hdm) the Coverage theorems consume. No
  emission↔discharge semantic gap.
- **V-iii (walk classification decidable + total):** `traceBundles`
  parallel to `clauses`; `none` at every `mkClause` (Solver.lean:369),
  `some` flushed only at the two learned sites (:1054/:1072 — the only
  `mkClause … true` sites). `bundles[cid].isNone ⟺ input clause`.
- **V-iv (R6 confirmed at the semantics level):** `IneqAtom.Holds` for
  `.eq` is `∃ f ∈ factors, evalP ρ f.1 = 0` (Check.lean:401) — the
  semantics NEVER forms the product; A1 multi-factor ¬EQ unfolds to
  per-factor `≠ 0` facts. factorSplit-ignorance is structurally
  invisible to the checker. Elaborator need: one named multi-factor EQ
  collapse helper (keeps the meta simp-set tame).
- **V-v (by-value decode surfaces all bridged):** explain-side poly
  constructions located: lc = `(p.coeffsIn y)[1]!` (Explain.lean:389),
  disc = raw `B²−4AC` (:406), pDiff = `managerNormalize (2·A·y+B)`
  (:407), degenerate reduct `q = B·y+C` (:413). Checker-side bridges
  all exist: R3 `coeffsOf_eq_coeffsIn_toList`, `evalP_discPolyOf`,
  `signMatches_managerNormalize` (Check.lean:1154), pDiff bridge
  (Check.lean:1198); `cellBound_plinear` links are evalP-level
  (Coverage.lean:198-199). Nothing new to prove for decode.
- **V-vi (no orphan steps in flushed bundles):** explain `none` ⇒
  `resolveLazyJustification` none ⇒ round aborts before flush
  (Solver.lean:914-917). Decoder orphan-rejection is dead code on real
  traces, kept as the sound direction.

**DECISIONS (Danielle-approved):**
- **R-i (glue, sharpened):** per arith clause, all-literals-fail
  yields (a) core-atom Holds unfoldings, (b) one rootCmp fact per
  encoding/cellBound step, (c) sign facts per sign literal, (d) root-
  order facts. ALL nonlinear products of ρ-values live INSIDE the
  discharge lemmas (Thom identity digested by `thom_discharge`); the
  glue only does sign-case evaluation + linear order reasoning over
  `{ρ y} ∪ {rootVal constants}`. **linarith-over-opaque-constants is
  the workhorse, nlinarith the backup** — try linarith first (smaller
  terms, faster kernel checks). Per-shape composition lemmas remain
  the recorded fallback. Glue failure = sound rejection.
- **R-ii (decoder reconstruction):** rebuild disc/pDiff/lc/reduct-q
  with the SAME MPoly expressions Explain uses → by-value atom
  matching holds by construction; bridge to checker forms via V-v
  lemmas. Decode failure = rejection (loud at F4). F4 pins assert
  decode success on every step of the acceptance traces.
- **R-iii (root-order injection):** group rootVal occurrences by
  (y, p); ≥2 indices in one arith clause ⇒ inject
  `quad_roots_order`/`quadRoot_le` facts for that group.
  Deterministic; the only cross-fact interaction the glue can need.
- **R-iv (step-to-marker accumulation):** walk bundle accumulating
  projection steps; `.arith` attaches + clears; `.clause`/`.decision`
  don't disturb; leftover steps at bundle end ⇒ reject (dead code per
  V-vi). factorSplit skipped during accumulation (R6);
  pseudoDivision/intBranch anywhere ⇒ reject bundle (R7/F0 `isV0`).
- **R-v (kernel cost, watch):** per-walk-step `upRefutes … = true` by
  `decide` runs over LOCAL F-sets (that bundle's antecedents + arith
  clauses), not cumulative — per-bundle kernel work, ~linear in
  refutation size. nla-16 measures.
- **R-vi (F-output contract for nla-14):** the F2/F3 artifact is
  `∀ ρ, (∀ C ∈ inputClauses, clauseHolds ρ atoms C) → False` over the
  INTERNAL-order snapshot atom table; goal-atom alignment is 14's job
  (it replays the same init → mapping reconstructible meta-side).
- **R-vii (12e note):** integer-branching learned clauses must flush
  bundles through the same two-site discipline when 12e lands; until
  then `intBranch` steps keep their v0 rejection.
- **R-viii (parity statement for the F assembly):** F2/F3 have no z3
  counterpart (z3 trusts its search); parity lives on the emission
  side — byte-pinned (12c/12d) + grammar-locked (E1). Checker
  contract: accept ⊇ grammar-admitted traces (completeness: E2 per
  constructor + F4 acceptance), accept ⊆ valid refutations
  (soundness: kernel + trusted lemmas only; all meta term-producing).

**Traps carried into implementation:** `(0 : ℝ)` numeral discipline
until F5's R1' normalization (leafNumeric glue hits const-poly evalP →
Int-cast numerals — same trap; `Int.cast_lt_zero.mpr`/`Int.cast_pos.mpr`
for cast facts); linarith before nlinarith (R-i); rootVals opaque.

