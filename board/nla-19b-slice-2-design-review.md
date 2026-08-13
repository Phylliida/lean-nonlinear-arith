## nla-19b Slice 2 design review `done` (2026-08-13 eve, Danielle-requested; post-Slice-2 divergence/regret audit)

Method: adversarial re-read of the Slice-2 diff + the untouched
helpers it routes through + z3 source re-read
(`nlsat_explain.cpp:280-330` add_simple_assumption, `:1030-1095` the
eq_info comment block, `:1096-1265` simplify, `nlsat_solver.cpp:586-620`
mk_ineq_atom). Lenses: regret-later, z3 fidelity, coverage gaps.

**FINDING 1 (REAL, pre-existing, search-side — boarded, not Slice-2's):
our `mkIneqAtom` port omits z3's `mk_ineq_atom` normalization loop**
(nlsat_solver.cpp:593-607: every factor `flip_sign_if_lm_neg`-normalized,
kind flipped on an odd count of odd-factor flips). Review 13's
"z3-faithful atoms never carry lm-negative factors" assumption is
FALSE for our pipeline — probe: `MPoly.flipSignIfLmNeg` on the o139
atom-1 factor returns its negation (lm-negative under gradedLexCompare),
and the dump stores it unflipped. Consequences: (a) atom dedup
divergence — z3 identifies `−p > 0` with `p < 0` post-normalization,
we create two atoms (more bool vars; propagation/decision paths can
diverge → witness-level, possibly conflict-count-level); search-side
untrusted layer, soundness untouched. (b) HAD the normalization been
ported, the A4/A5 lc atoms would carry `−lc` (kind-flipped) and the
Slice-2 lane's by-value lc lookup would silently miss. **Boarded for
the 12c-fidelity/nla-16 lane** (porting it now would churn every
pinned trace mid-19b; nla-16's harness is the measurement gate).
**Slice-2-side mitigation LANDED (the R-d idiom):** the lc evidence
lookup is negation-tolerant — `lcNeOf`/`lcSignOf` fall back to
`lc.neg` via the new `signFlipFactFor` (`evalP_neg` + `Left.neg_pos_iff`/
`pos_of_neg_neg`; `Eq.mp` forward per the G11 lesson) and the existing
`diseqFactFor`. Belt-and-braces today, load-bearing when the
normalization port lands. Pin: the s2nf fixture (eq = −x0x1²+1, lc =
−x0, the clause's A4 literal carries `x0 > 0` — the normalized form of
"lc < 0"; firing confirmed instrumented, then reverted).

**FINDING 2 (coverage pin added):** the Slice-2 pins exercised only
single-replacement rebuilt literals; z3 rewrites EVERY deg-≥k factor
of a literal (one step each). The s2tr fixture pins the two-replacement
+ kept-factor transport (firing confirmed instrumented, then reverted).

**VERIFIED CLEAN (with anchors):**
- A4/A5 polarity at the source level: `add_simple_assumption` creates
  the single-factor ODD atom and literal `(b, !sign)` (:286-292) —
  A5's `add_assumption(EQ, lc, true)` ⟹ the unnegated EQ atom in the
  clause (R-h ✓, and the diseq extraction path); A4's default-sign
  LT/GT ⟹ the negated lt/gt literal whose failure yields the positive
  comparison (exactly the `signPos` index shape ✓).
- The eq_info comment block (:1041-1067) documents EXACTLY the pdSign
  family + `pdSign_eq` shapes (the EQ case needs only `lc ≠ 0`) — the
  Slice-1 hole the Slice-2 `pdSign_eq` closed is z3-documented.
- `add_lc_diseq` first-call-wins with ineq upgrade (:1089-1093): the
  per-core shared assumption is ineq iff ANY factor requested it —
  the ineq (sign-pinned) is stronger and serves the diseq cases ✓ the
  lane's evidence priority (signPos → diseq) is compatible either way.
- The flip rules compose: rule 1 (:1132-1137, before the const check)
  + the const-case flip (:1170-1172) — the lane's σ = lc-sign ·
  remainder-sign fold matches both.
- The transport construction (fresh-eyes re-read): position fold
  order (reverse-cons = forward), σs alignment (consEven pushes literal
  1), hk Or-side pinning, Iff.mpr direction (transport target is the
  ORIGINAL side), mt for the ¬Holds side, `Iff.refl` for kept
  positions, closeSigProd sandbox (hasMVar + withoutModifyingState),
  `Eq.refl`-proof kind equalities (same-ctor exprs). Duplicate/false
  matches produce only valid facts (sound); the participation-not-trust
  discipline holds throughout.
- The extractFacts split is behavior-preserving (the only
  classification change is single-factor lt/gt positive → `.signPos`,
  consumed only by the new index); full-build zero churn confirmed.
- Axioms: `holds_signRel`/`holds_zeroRel_eq`/`pdSign_eq`/`realSign_mul`/
  `SignRel.sign_oddProd` all depend only on
  [propext, Classical.choice, Quot.sound] (#print axioms probe).
- Fuel: transports preserve per-literal factor counts (drops never
  inserted); the +2·|pdSteps| drop-lane margin is bundle-sized.

**Residual (unchanged from the Slice-2 entry):** the mixed-literal
attribution note (const-drop + rebuilt in one literal) and the
glue-strength data point (x0⁴=0 stalls the cone). New watch item:
FINDING 1's normalization port will change atom shapes → the
WalkTests/RefuteTests snapshots re-derive then (expected churn, not
breakage).

