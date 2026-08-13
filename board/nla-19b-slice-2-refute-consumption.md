## nla-19b Slice 2 `done` (2026-08-13) — Refute consumption: rebuilt-literal equivalence transport + drop lane

All Slice-2 items landed per the boarded plan. Full build green, zero
snapshot churn (every pre-existing pin re-green — the extractFacts
split is behavior-preserving).

**Trusted (Check/Discharge.lean, after the pdSign family):**
- `pdSign_eq` — the PARITY-FREE zero-status transfer (`L^d·F = Q·E+R`,
  `E = 0`, `L ≠ 0` ⟹ `F = 0 ↔ R = 0`). **Coverage hole found in the
  Slice-1 family:** z3's `kind == EQ` case adds only `add_lc_diseq`
  (:1176-1184), so for an EQ-kind rebuilt literal with d odd and a
  sign-free non-const lc, NO Slice-1 member applies (`pdSign_even_eq`
  needs d even; the `odd_{pos,neg}_eq` pair need the lc's sign). The
  Slice-1 review's "pdSign_*_eq is parity/sign-invariant" claim was
  wrong for the d-odd sign-free case; `pdSign_eq` closes it (and is
  used for ALL zero-status needs — the odd/even eq members stay for
  the packs).
- `SignRel`/`ZeroRel` inductives + `holds_signRel`/`holds_zeroRel_eq`:
  the rebuilt-literal equivalence transport. Per-position evidence
  relates a meta-reconstructed ORIGINAL factor list to the rebuilt
  (clause-visible) one: `consOdd` (zero-Iff + sign relation
  `sign f = σ·sign r`, σ ∈ {±1}) / `consEven` (zero-Iff only — even
  factors are sign-absorbed, :1133, and z3 adds no sign assumption for
  them). `oddSigProd` is z3's running `atom_sign` (:1113/:1136/:1171);
  the kind relation is an hk hypothesis discharged against the
  concrete σ list, so a flip miscount fails to elaborate, never
  produces a wrong fact. Helpers: `realSign_mul` (not in mathlib's
  `Real.sign` API), `realSign_eq_{one,neg_one}_iff`,
  `pdSign_pack_{pos,neg}`, the comparison transports.
- Source fidelity (:1096-1216 re-read this session): kept factors
  (deg < k) verbatim :1124-1128; non-const remainder REPLACES with the
  mark preserved :1186-1190; const-nonzero DROPS the position
  :1163-1185; const-zero collapses the literal with early return
  :1149-1162; flip rule 1 (:1132-1137) fires BEFORE the const check,
  the const-case flip (:1170-1172, `s < 0 ∧ !is_even`) after — they
  compose; `l.sign()` re-applied :1193-1195; ONE lc assumption per
  core :1257-1263.

**Meta (Nlsat/Refute.lean):**
- `extractFacts` split into `extractPosFacts`/`extractNegFacts`
  (Holds/¬Holds proofs directly) + a polarity dispatcher — the pd lane
  re-extracts transported facts through the SAME code path (no
  duplicate extraction logic). New `FactKind.signPos` indexes the
  positive single-factor comparisons (the A4 lc-sign evidence).
- `pdRewriteLane` (after `collectStepFacts`, before the closes): the
  **transport lane** matches rebuilt-atom factors against step
  remainders by value, builds `SignRel`/`ZeroRel` derivations
  (identity via `pseudoDivisionIdentity`, `lc ≠ 0` from the A5 diseq
  literal or const-decide, lc sign from the A4 literal — the `signPos`
  index), transports `Holds` to the reconstructed original factor
  list, re-extracts, notes into the standard indexes. The **drop
  lane** (const remainders) notes `f = 0` (path-(b) collapse),
  `f ≠ 0` (always, lc ≠ 0 suffices), and the definite sign when the
  evidence determines σ. Path-(c) keep-original: unmatched steps are
  inert (pinned). State threaded through a `PdState` record —
  `withContext` closures can't assign captured `let mut`s.
- Fuel: the transport preserves per-literal factor counts (drops are
  never inserted — see the residual below), so transported diseqs stay
  inside the review-11 per-literal bound; the budget gains
  `2·|pdSteps|` for the drop lane's definite facts (bundle-sized).

**⚠ Trap (cost ~1h, self-inflicted but the lesson is general):** the
corrupt-payload probes first showed kernel "declaration has free
variables '_tmp✝'" — chased as a closeAlgRefl mvar-pollution bug
(pre-ring-throw bisect "confirmed" it) — but the isolated repro was
clean both ways: '_tmp✝' free-variable kernel errors are ELABORATION
ERROR-RECOVERY artifacts (an unknown identifier upstream — my scratch
dropped the `pd1Atoms` def in an overwrite). Check for
`unknown identifier` FIRST when a kernel free-variable error appears.
The `withoutModifyingState` rollback added to
`closeAlgRefl`/`closeNumerically`/`closeSigProd` during the hunt is
kept as defense-in-depth for the Slice-1 hole class (a failing
ring/norm_num leaves the sandbox mvar assigned to a partial chain;
rolling the mvar table back is strictly cleaner) — behavior on the
success path is unchanged (the term is extracted before rollback);
full build re-green.

**Pins (RefuteTests 19b-Slice-2 section):** pd1/pd3/pd6/pd2/pd4 arith
members from the real dumps with steps (transport fires — confirmed by
temporary instrumentation, reverted: pd3 = reorder + square-lc A4 +
bound-literal target; pd6 = d even + A5 diseq at the R-h polarity;
pd2/pd4 = drop lane both families); corrupt-f (identity throws →
sound skip → glue closes); lcSign-hint flip and isEven-hint flip
(decision-1: both untrusted — marks come from the atom, signs from the
evidence); path-(c) extra-step tolerance; R-h polarity flip (⟨6,true⟩
⟹ evidence gone, transport inert, valid clause still closes);
ZeroRel (eq-kind rebuilt literal); kind-flip + d = 3 (σ = −1 via the
A4-LT literal); consEven (even-marked replaced factor in a multi-factor
rebuilt atom); an invalid-clause negative probe (rejects).

**Glue-subsumption finding (worth nla-16's attention):** every Slice-0
driver's arith member ALSO closes step-free — the F2 glue (nlinarith +
eq×var lift + ineq×ineq pairing + sq_nonneg hints + lazy trichotomy
splits) subsumes the pseudoDivision transport on these small cores
(step-free variants pinned as documentation; guards fail loudly if
either side regresses). The transport's value is harder instances and
z3-faithful coverage — its content is pinned by the firing
confirmations + the hint-flip pins.

**Residual (recorded, not new gaps):** (i) const-dropped positions are
handled by the GLOBAL drop lane, not attributed to a specific rebuilt
literal — a MIXED literal (one factor const-dropped, another rebuilt
in the same literal, unexercised by any live driver) gets the
cons-only transport whose computed original kind may differ from z3's
by the dropped position's flip contribution; every noted fact is still
kernel-proven (sound), only the coupling through the dropped factor is
lost, and the drop lane's definite-sign fact restores it
glue-mediated. Synthetic-fixture territory; board as G5-residual if a
driver ever emits it. (ii) The glue-strength data point: `x0⁴ = 0`
branches stall the cone (no root-taking) — shaped the consEven fixture
(even factor x0⁴+1).

**Next: Slice 3** — pin each driver's emission shapes (done above:
the census table + these pins), drop `pseudoDivision` from the
`isV0`/`Walk.precheck` reject set (intBranch stays gated → 12e),
acceptance = pd1 AND o139 walked end-to-end (o139 half DONE), G5 flips
done, M3 declared per DESIGN-endgame tiers.

