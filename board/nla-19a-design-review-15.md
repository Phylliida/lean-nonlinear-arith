## nla-19a design review 15 `done` (2026-08-10; G4 census slice COMPLETE — items 3/4 + audit)

**Item 3 (step-fact collection) DONE** (commits 35ba5ae, fd0e46c,
2c71c63): the cross-links member is closed. `Refute.collectStepFacts`
runs per `.arith` marker with the bundle's preceding projection steps
(Walk `buildFSet` accumulates them — the `ResolutionAntecedent` doc was
already written for this coupling), and for each encoding step matched
against an extracted root fact `(k, y, i, p)` converts the opaque
`rootCmp k (ρ y) (rootVal ρ y i p)` into glue-ready first-order facts:

- **linearRoot** (direct + encoding-free): `coverage_linearRoot`'s iff
  reversed by a native `(k, mkNeg)` polarity table (`not_not` vs `mt`
  — caught an inversion: `¬SHolds ρ a true = ¬¬Holds` routes through
  `Iff.mp not_not` FORWARD, not `mt`; the emitted polarity table is
  `eq/lt/gt → true`, `le/ge → false`-kind-flips).
- **linearRoot, sa = 0 degenerate reroute** (z3 :811-812, E1): parent
  deg-2 root fact + step on the reduct `q`; transport across
  `rootVal_eq_degenerate` + coefficient links + `rootVal_eq_linear`;
  the A = 0 clause sign literal is load-bearing (`findSignFact`
  sign-0 lock; skips soundly if absent).
- **encoding-free lane** (foreign traces, grammar-free): deg-1 const-lc
  root facts convert unconditionally via `rootVal_eq_linear` +
  `linearRoot_discharge` (numeric hAq from the const lc) — z3 routes
  such roots through `mk_linear_root`, so this region is
  foreign-trace defense.
- **thomQuadratic**: `thom_discharge` + `rootVal_eq_quad` — the iff at
  RAW-COEFFICIENT form (B²−4AC accessors), NOT via
  `coverage_thomQuadratic`'s `discPolyOf p y` application spelling:
  the same kernel-reduction trap (the app's value is not
  kernel-computable), so the disc-sign evidence is built in the
  EXPANSION form (`mkValueFact`-style two-hop); the clause lane's
  comparison on the by-value `discPolyOf` literal moves onto the
  expansion's value form through the ring identity (`closeAlgRefl` —
  mangle + `ring`). Then `leadSgn` resolved via the new
  `leadSgn_of_pos`/`leadSgn_of_neg` and the coeff accessors rewritten
  (`hL, hC2, hC1` at the noted fact), so the mangle's
  `simp only [thomFormula]` (probed: concrete-ctor cases unfold) yields
  Or/And of comparisons the `findOr`-splitting glue consumes.

**Tickets (decide-grade, verified per consumed step):**
- grammar: thom via plain `grammarOK`-decide (`mkThomGrammar`); linear
  via `mkLinearRootGrammar` — the kernel CANNOT decide `grammarOK`'s
  `coeffsIn` branch (`MPoly.add` wf-compilation wall), so the condition
  is constructed from the item-2 reducer chain +
  `coeffsOf_getElem!_eq` (E1-reachable lanes both covered: const-lc
  `none` and the `(c, s)` const/non-const lanes).
- canonicity: **new decidable mirrors** `Monomial.canonOK` /
  `MPoly.canonOK` + soundness (TypesOrder) — head-vs-head
  strict-increase checks suffice by transitivity; canonicality of
  payload data is the checker boundary's decide ticket the Semantics
  docstring always promised.
- **precheck gate (Walk):** every bundle's steps must pass `grammarOK`
  (native compute) — the walk-level grammar enforcement; corrupted
  payloads reject before any discharge work.

**Traps hit along the way (recorded):** `matches` is a reserved word
(like `lemma`); `toExpr RootKind`/`TraceStep` don't exist (hand-quote:
`rootKindToExpr`/`thomStepToExpr`); `mkAppM ``decide` does NOT
synthesize the `Decidable` instance (`mkAppOptM … #[some lt, none]`);
`Eq.trans` can't serve as Prop transport through a congrArg'd
prop-family (`Eq.mpr` is the combinator); `Or.inr`/`Or.inl` with
unpinned side Props leave HOU mvars ("result contains metavariables" —
pin side types); `v < 0` is a Prop, `decide (v < 0)` the Bool;
`OfNat.ofNat`'s raw literal is Nat (`toExpr (1 : Nat)`, not Int);
`whnf`-indexing into em-projections panics (rebuild Holds
propositions natively instead).

**Audit fixes en route:** fuel sizing for step-formula Ors (the
review-11 budget counted only clause facts — now
`(clause-part + 4) · 2^thomOrs`); `Grammar.linearRoot`'s implicit
binders must be pinned (`mkAppOptM`) or the match on `?lcFact` can't
reduce; polarity-table inversion (caught by the lt fixture) — both
routes pinned by the lt/eq/ge/le fixtures.

**Item 4 (F-w probes) DONE:** mkNeg corrupt (grammar-BREAKING, const-lc
fold) → reject; sq = 0 vs const disc = 8 (grammar-clean, semantic
mismatch) → skip ⟹ load-bearing reject; sq = 0 with sp = −1 (E1
placeholder pin, grammar-BREAKING — also pinned at precheck by the
xl-final grammar-gate probe) → reject; sq corrupt AND sp restored
(grammar-clean) → still rejected semantically. sp itself (sq > 0, all
ranges valid, value corrupted) is NOT consumed by the discharge
certificates — documented accepted-trace-superset fact: accepted
traces carry only kernel-checked TRUE cross-links (review-6 F-w
semantics).

**Fixture inventory (all pinned, Refute + Walk):** thom const lane
(x0²−2), thom clause lane (multivariate, the by-value
discPolyOf/pDiffPolyOf reconstruction consumed), linear lt/eq/ge/le
(the full kind×polarity table), degenerate reroute const-lc,
degenerate reroute non-const-lc (the clause lane), encoding-free
foreign bilinear, plus per-fixture load-bearing negative probes and the
xl end-to-end walk fixture with load-bearing + grammar-gate variants.

**Adversarial addendum (Danielle's divergence probe, 2026-08-10):** the
split-fuel `thomDisjunctive` table was verified cell-by-cell against
`Semantics.thomFormula` — the un-pinned le/ge Thom cells were the one
place a divergence could plausibly hide (nonstrict kinds don't use
z3's strict-region + boundary decomposition; the ≤-forms absorb the
boundary: `le 1 := 0 ≤ pv ∧ pdv ≤ 0` conjunctive, `le 2 := pv ≤ 0 ∨
(0 ≤ pv ∧ pdv ≤ 0)`, `ge 1` disjunctive, `ge 2` conjunctive). The fuel
table matched every cell. The le/ge Thom lane is now PINNED too
(both-bounds-on-the-greater-root fixture: ge-2 conjunctive versus the
`y > 0`/`p < 0` literals, le-2 disjunctive exercised through findOr).
No off-board divergences were found in this audit — the remaining
known items are all boarded (sp-superset semantics, the deliberate
encoding-free lane, R-q, sq=0 Thom fixture, G5/6/7+G8/9/10 owners).

**Honest inventory (recorded, NOT new gaps):**
- rootCount EVALUATION lane (count comparisons like `2 ≤ rootCount` for
  const-coefficient deg-2 — e.g. an `i = 2` root atom on a double-root
  poly with disc = 0): no current consumer (the count side is only
  probed for count = 0 lanes, item 2). The thom iff stays valid
  `i ∈ {1, 2}`-parameterized, but a contradiction sourced ONLY from the
  count side against the constant-data rootCount function would need a
  `rootCount_eq_one` family. → **R-q**, parked as checker-completeness
  candidate for nla-16 measurement (no live or synthetic witness in the
  z3-faithful grammar region — rootCount > 0 with sq-payload evidence
  drives all z3-faithful contradictions through formula facts).
- sq=0 Thom fixture not pinned (grammar admits it; production supports
  it; the count-side issue above is orthogonal). Cheap to add if
  wanted — no z3-source reachability question: :806 accepts sq = 0
  (rejects only sq < 0), and i ∈ {1, 2} is grammar-pinned.
- `mkThomGrammar`'s decide ticket is cheap (`degreeIn` + Int/Bool
  ranges, no polynomial arithmetic); `mkLinearRootGrammar` rides the
  reducer (small).

**z3-fidelity verdict:** the step shapes consumed match the emission
grammar one-to-one (linear/Thom, both degenerate tiers); the
no-production steps (`factorSplit` R6, `cellBound` R5/V-a,
`leafNumeric` F3) contribute nothing, as boarded. The generic-encode
lane produces only facts derivable from the atom semantics directly
(no z3 counterpart by design — checker-side completeness insurance for
foreign traces, sound by kernel checking).

