## nla-19a `active` (opened 2026-08-01) — checker v0 + Q1 coverage proof (12d twin)

Trusted layer (no assume/admit/external_body). Two files land in this
arc: `Nlsat/Trace.lean` (the 8-shape language: leafNumeric /
thomQuadratic / linearRoot / cellBound / pseudoDivision / factorSplit /
intBranch / resolution — DESIGN-nlsat-quadratic §2; **payloads pin
against the checker, never before**) and `Nlsat/Check.lean` v0.

**Discharge map (v0):**
- `leafNumeric` → nla-09 certificates: `checkNoRoot_sound` /
  `checkUniqueRoot_sound` / `checkPosOn_sound` / `checkNegOn_sound`
  (`Certificates/Sound.lean:286/313/376/393`), certs discharged
  `by decide`.
- `thomQuadratic` → S3 kit (`Templates/Quadratic.lean`, 12 lemmas):
  `quad_key` completing-the-square instance + the sign-dictionary iffs
  both lead signs + the definite-disc cases.
- `linearRoot` → plain inequality lemmas (exact mk_linear_root
  arithmetic, incl. the LE/GE kind-remap + literal-negation fold at
  nlsat_explain.cpp:869-878).
- `cellBound` → the S3 4-lemma point-vs-root ordering family
  (`quad_{left,right}_of_{inside,root}`) + `quad_roots_order` +
  linarith glue.

**Q1 (grammar-first, prove-over-empiricism):** the emission grammar is
now enumerated FROM SOURCE (nlsat_explain.cpp@4.12.5): ineq shapes
A1–A5 (multi-factor ¬EQ from add_zero_assumption :280; single-factor
sign assumptions :289; rebuilt core literals from normalize :471 and
simplify :1194; lc ineq/diseq from simplify :1259/:1261), root tiers B
(linear→ineq :861-879; Thom → pure sign assumptions on {disc, A,
2Ay+B, p} :787-820; generic mk_root_atom fallback :732), cell literals
C (ROOT_EQ early-return :936-937; ROOT_GT/LT bounds :965/:968, GE/LE
under full_dimensional; 1-based indices). Formalize this grammar in
Lean and prove the S3-coverage lemma against it during 19a; if the
grammar exceeds the current S3 family, extend the family first (same
Templates/Quadratic style).

**v0 scope tension (stated, not a divergence):** with
simplify_cores=true and factor=true (nra defaults), real conflicts can
emit `pseudoDivision`/`factorSplit`/`resolution` steps — those
discharge in 19b. The v0 checker marks them undischarged; 19a's
end-to-end acceptance targets conflicts whose traces stay in the four
v0 shapes.

**Trace egress design question (pins during 19a, not before — rule
3):** how the trace leaves SolverM — a `trace : Array TraceStep`
solver-state field that explain appends to vs. ExplainFn returning
(literals × steps) — and the checker's theorem shape (per-step
discharge lemmas composing into the learned-clause theorem).

**DESIGN REVIEW 2026-08-03 (Danielle-approved, pre-implementation) —
five decisions, F1–F5:**

- **F1 egress = buffer + per-learned-clause bundles (refines option
  (a)).** NOT a flat global log: `resolve` runs multiple analysis
  rounds per call (the `goto start` loop, Solver.lean:1005/:1022) with
  TWO learned-clause creation sites (:1002, :1019), aborted rounds
  whose partial steps must be discarded, a UNSAT exit that creates no
  clause (:993 `lemma.isEmpty`), and the `lemmaIsClause` shortcut
  (:1013) that terminates a derivation by REFERENCING an existing
  clause. Shape: `Solver.pendingTrace : Array TraceStep` appended by
  ExplainM (free lift — `ExplainM = StateT ExplainState SolverM`) and
  by resolve's resolution bookkeeping; CLEARED at each `start:` round
  reset (:946 — z3's own `m_lemma`/`numMarks` reset boundary, so this
  is also the faithful bundling boundary); flushed into
  `traceBundles : Array (Option TraceBundle)` PARALLEL to `clauses`
  (the `justifications : Array Justification` precedent; `Clause` in
  Types.lean untouched) at both mkClause sites, and into a designated
  `finalRefutation` field at the empty-lemma exit. Payoffs: refutation
  DAG explicit (checker walks cids from `finalRefutation` — no DAG
  reconstruction in TRUSTED code); aborted rounds self-discard;
  `delClause` retention falls out free (append-only table, DRAT-style
  references to later-deleted clauses still resolve). Parity argument:
  append-only observation, no control-flow reads; all 12c/12d pins
  stay byte-identical. `ExplainFn` signature unchanged; mockExplain
  untouched.
- **F2 reorder interaction: extraction seam BEFORE restoreOrder.**
  Trace payloads are in INTERNAL variable order; `restoreOrder`
  renames atoms back and deletes learned root-atom clauses. Verified
  invariant (pin as regression test): reorder fires exactly once per
  `check()`, before `searchCheck` (Solver.lean:1242) — never
  mid-search — so all bundles in one search share one indexing. UNSAT
  extraction happens in the seam between `searchCheck` and
  `restoreOrder` (:1245-1247); Γ is stated in internal order; mapping
  back through the permutation is the tactic layer's (nla-14)
  responsibility.
- **F3 fragment gate is CHECKER-COMPUTED, not search-asserted.** The
  S1-gated mark on a trace step is advisory (stats, nla-11/13 deferral
  routing); the checker independently recomputes fragment membership
  from payloads (top-var degree ≤ 2 is decidable data) and has no
  discharge outside it. A corrupted/lying mark → rejection, not a
  wrong theorem. Closes the trust hole in the earlier "search marks,
  checker trusts" framing.
- **F4 Q1 grammar: proved direction is grammar→S3 ONLY.**
  Explain→grammar is a claim about UNTRUSTED search code — it stays
  source-fidelity + pins (verifying it = verifying the search, not the
  trust model). The grammar doubles as the checker's INPUT CONTRACT:
  out-of-grammar step = parse-level rejection (the sound failure
  mode). Formalized as an inductive predicate over payloads with
  per-constructor source line refs (RULES.md provenance discipline);
  19b extends grammar + coverage in the same pattern.
- **F5 emit all occurring shapes NOW, discharge later.** With
  factor=true/simplify_cores=true defaults, `factorSplit` /
  `pseudoDivision` / resolution steps OCCUR TODAY — emission can't be
  deferred, only discharge. All 8 payloads pinned in this arc
  (emission-side); resolution emission is nearly free (ordered
  antecedent list: cid or arith-lemma ref, per round). RISK
  (accepted): if a √2-grade acceptance goal emits `factorSplit` (Yun
  splits repeated factors, e.g. x²+2x+1), that discharge pulls forward
  from 19b. Mitigation: pin which shapes each acceptance goal emits;
  x²−2 is square-free so planned goals stay in-fragment.

**Checker architecture (F-companion):** term-producing elaborator in
the nla-09 house style — per-step lemma applications composing into
`Γ ⊢ False` with Γ over a `Nat → ℝ` valuation — NOT a reflected Bool
checker for the whole refutation (reflecting real-algebraic semantics
is nla-11 territory). `decide`-grade only at `leafNumeric` leaves via
the nla-09 bridge.

**Slice order (rule-3 literal):** grammar draft → egress decision
recorded → trace datatype → PER-SHAPE INTERLEAVE (linearRoot →
thomQuadratic → cellBound → leafNumeric: emit + discharge + pin each)
→ coverage lemma last (grammar stable by then) → acceptance.
Emission-fidelity rule: justifications recorded AT z3's
literal-creation points, never reconstructed post-hoc (the LE/GE
remap + negation fold, atom::flip double-negation sites, and
negated-clause-literal polarity are where reconstruction would
quietly diverge).

