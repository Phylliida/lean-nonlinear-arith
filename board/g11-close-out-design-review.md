## G11 close-out design review `done` (2026-08-11 eve; Danielle-requested divergence/regret audit of the G11 close-out)

Method: adversarial re-read of the day's diff + the untouched helpers
it routes through, plus a source re-read of the root-atom emission
chain (`git show z3-4.12.5:src/nlsat/nlsat_explain.cpp:700-870`).

**Fidelity verdict: no z3 divergence possible from the diff.** Every
change is checker-side meta (`Refute.lean`) + trusted lemmas
(`Check/Discharge.lean`) + pins; the search/explain layer is
untouched (zero snapshot churn). The checker's F-w superset contract
stands: wrong conversions throw at `mkAppM` and skip; only
kernel-checked facts are noted. The trusted lemmas match z3's own
encoding shapes by construction: `mk_linear_root`'s emitted literal is
`k` applied to `p` (or `neg p` when the const lc is negative) —
exactly the Pos/Neg discharge RHSs `rootCmp k (±evalP ρ p) 0`.

**Source findings (emission-chain census, :725-818):** root ATOMS are
emitted only when `mk_linear_root` (deg-1, const-lc only) AND
`mk_quadratic_root` (deg-2, Thom) both fail — i.e. deg-1 NON-CONST-lc
(G11's case) and deg ≥ 3 (G7/Tier B); the emitted literal is always
NEGATED (`literal l(b, true)` :735). `ensure_sign` is called ONLY in
the quadratic path (q/A/p_diff/p) — **the deg-1 non-const-lc root
atom is emitted with NO lc guard**: the lead's sign is not
structurally present in the clause. (cid 7/9 got it from the clause's
own `⟨3,true⟩` — contingent, not guaranteed.) Deg-2 root atoms on
real traces: unreachable (sq < 0 at the sample ⟹ no roots ⟹ the poly
never enters add_cell_lits); documented non-issue, same disposition
as R-c. This census also VALIDATES the G11 lane split: deg-1
const-lc → `linearRoot`/encoding-free lane; deg-1 non-const →
rootGeneric/negRoot lanes; deg-2 → Thom.

**Findings — TWO REAL completeness gaps + one waste, all FIXED:**
- **F-i (positive side, clause `A = 0` fact):** the
  `rootGenericStepProduce` `some (0, …)` case noted NOTHING with the
  comment "the glue closes via that diseq clash" — but nothing
  produced the diseq (the rootPair fact is glue-opaque, and
  `rootDefiniteClose`'s deg-1 lane only fires on a LITERAL-zero lc).
  Overclaiming comment + dropped cross-link. Fixed: the lane now
  notes the lead's concrete-spelled `< 0 ∨ > 0` trichotomy
  (`ne_of_one_le_rootCount_deg1` + forward transport +
  `lt_or_gt_of_ne`); each findOr branch dies on the `A = 0` fact.
  Pin: `g11zAtoms` (root literal + `x1 = 0`) — closes; pre-fix it
  rejected.
- **F-ii (both sides, NO sign fact for the lead):** the negative
  side's fallback noted the disjunction with the comparison left
  `rootCmp`-OPAQUE (a guaranteed-dead leaf whenever the close needs
  the conversion — asymmetric with the positive side's two-sign
  disjunction). Fixed: new trusted `negHolds_deg1_trichotomy`
  (`A = 0 ∨ (0 < A ∧ ¬rootCmp (evalP p) 0) ∨ (A < 0 ∧ …)` — built
  from existing lemmas, no new axioms) as the fallback. AND the fix
  exposed a second, shared latent bug: the disjunctions' sign
  CONJUNCTS are accessor-spelled (`evalP ρ (coeffsOf …)[1]!`), whose
  redex stalls the mangle's evalP unfold — the `A < 0` dead-end leaf
  then can't die (its contradiction is sign-vs-clause-fact). The
  positive side's pre-existing disjunction fallback had the same
  latent defect (never pinned). Fixed: `mkSignTransports` (+ `idLam`)
  map both sign conjuncts through the bridge to the concrete spelling
  at note time, in both lanes. Pins: `g11tAtoms` (negative, no sign
  fact — pre-fix rejects, post-fix closes) and `g11uAtoms` (the
  positive two-sign fallback, previously unpinned).
- **F-iii (negative side, clause `A = 0` fact):** the identity-Or was
  noted although `¬Holds` is VACUOUS when `A = 0` (rootCount = 0) —
  a redundant split, wasted fuel. Now skips with the vacuity
  argument recorded. No behavioral pin (pure fuel).

**And-hyp splitting:** the disjuncts are `sign ∧ comparison` Ands;
the failing-leaf dumps confirmed the glue sees them unsplit per
branch — the closes work because each leaf's contradiction needs only
ONE conjunct (content leaves use the comparison, dead-end leaves the
transported sign). No And-splitter needed; recorded as the reason
the transports were load-bearing.

**Verified clean by re-read:** the `disjArgs[0]!`/`[1]!` Or-arg
indexing; the `Eq.mp`-forward / `Eq.mpr`-backward transports (all
four sites rechecked against core signatures); `mkCoeFactEq`'s
`mkExpectedTypeHint` pin (kernel-checked either way — the ascribed
type is defeq or it throws and skips, sound both ways); fuel sizing
(the 3-way needs ≤ 2 findOr splits; root literals contribute 2 each
+ margin); the walk's cid-7 Pos-lane comment (the `0 < A` sign fact
IS present there via `⟨3,true⟩`, so the Pos discharge fires — the
comment stands).

**Watch items (no change, recorded):** (1) the lanes' silent
`try/catch` discipline hides runtime throws — the instrumentation
recipe (log the catch + leaf dump) is in HANDOFF; a lane-skip stats
counter is an nla-16 candidate. (2) The eq × bare-var lift notes
`|eqFacts| × |vars|` hyps indiscriminately — a relevance filter is a
G8-adjacent candidate if nla-16 shows glue pacing drift. (3)
rootPair facts for deg ≥ 3 stay G7/Tier B.

**Residual inventory after this review:** within the deg ≤ 2 fragment,
both root-literal polarities at deg 1 are fully covered (sign-locked,
sign-free trichotomy, clause-`A = 0`), const-lc via the encoding-free
lane, deg-2 via Thom. No known rejection class remains for ineq/root
atoms in v0 traces; the standing gaps are unchanged (G5/19b
pseudoDivision — in flight, G6/12e, G7/Tier B, G8–G10/nla-16).

