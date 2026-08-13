## nla-19b Slice 1 `done` (2026-08-13) — grammar + identity close + sign-transfer family; the closeAlgRefl HOLE bug

All three Slice-1 components landed per the boarded plan and decision
1 (structural-only grammar + per-instance discharge; d-parity/lcSign
never trusted). Full build green 7612, zero snapshot churn.

**Grammar (Trace.lean):** `Grammar.pseudoDivision` gains the three
structural decide-grade conditions: `lcSign ∈ {−1, 0, 1}`, the
const-lc sign agreement (`lcSign = Int.sign v` when the lc —
`(eq.coeffsIn x)[eq.degreeIn x]!` — is a const `v`; mirrors
`linearRoot`'s lcFact shape), and the pseudo-remainder degree-drop
`r = [] ∨ r.degreeIn x < eq.degreeIn x` (:5095's contract). The
kernel-reduction wall only shows up at the const-lc `coeffsIn` branch,
exactly as in `linearRoot` — the precheck's NATIVE grammarOK
evaluation handles it; a kernel-decide ticket (if Slice 2 wants one)
needs the reducer bridge, `mkLinearRootGrammar` precedent.
`grammarOK` mirror + `grammarOK_sound` case (the asConst? dance
copied from the linearRoot proof).

**Sign-transfer family (Check/Discharge.lean, 15 theorems):**
`pdSign_{even, odd_pos, odd_neg}_{lt, le, gt, ge, eq}` over ℝ —
z3's :1132-1137 rule cross-checked line-by-line (d even ⟹ sign f =
sign r; d odd ⟹ sign f = sign(lc)·sign r — pd1/pd2/pd3/pd4/pd6 all
match). Each takes the identity `L^e * F = Q * E + R`, `E = 0`, and
the lc evidence (`L ≠ 0` / `0 < L` / `L < 0`) as hypotheses — parity
and lcSign are payload hints; any identity witness yields the same
conclusion (the decision-1 perturbation property). Built from
`Even.pow_pos` / `Odd.pow_{pos,neg}_iff` + the mul-Iffs; the
const-remainder path-(b) collapse is the `eq` shape at `R = 0`.

**Identity close (`Refute.pseudoDivisionIdentity`):** Q recomputed
natively (`MPoly.pseudoDivisionCore … quotient=true` — untrusted,
native-only), the identity stated at the VALUE level with the
payload's OWN d/r and the concrete lc (`(evalP ρ lc)^d · evalP ρ f =
evalP ρ Q · evalP ρ eq + evalP ρ r` — no kernel-pow, no lcPowMul
poly; the literal exponent is ring-native), kernel-closed by the
closeAlgRefl idiom (evalP simp + `ring` — complete for these
identities, so genuine emissions always close; corrupt payloads throw
and skip).

**⚠ REAL BUG FOUND by the corruption probe — the closeAlgRefl HOLE:**
the probe ("corrupt remainder must throw") was ACCEPTED. Diagnosis:
`ring` assigns the goal with its normalization congruence chain
BEFORE the final rfl close, so a failure leaves the goal mvar
assigned to a term ending in an UNASSIGNED sub-mvar
(`Eq.mpr congr (Eq.mpr congr ?m)`) while only logging the error —
`closeAlgRefl`'s `unless isAssigned do throwError` then "succeeds",
returning a holed "proof" of a FALSE equation. Soundness intact by
the kernel backstop (holed terms can never reach a final checked
term — the green builds remain sound), but the clean skip-and-reject
discipline was broken, and any result-discarding consumer saw a false
accept. Fixed at all three term-producing sites (`closeAlgRefl`,
`mkValueFact`, `closeNumerically`): check `hasMVar` on the
instantiated term, not just `isAssigned`. Regression pin: the
closeAlgRefl-on-a-false-equation probe in the Slice-1 test block.

**Pins (RefuteTests 19b-Slice-1 section):** 6 grammar #guards
(genuine pd1/pd6 payloads pass; lcSign out of range, const-lc sign
mismatch, and degree-not-dropped r all reject); pd1/pd6 identities
close with lc sanity checks; the decision-1 perturbation witness
(pd1 at d = 2) closes; the corrupt remainder throws; three tactic
integration examples firing `pdSign_odd_pos_gt` (pd1),
`pdSign_even_lt` (pd6), `pdSign_odd_neg_gt` (pd4's const-r flip
payload).

**Slice-2 notes (carried):** the consumption flow per the boarded
plan — match rebuilt-literal factors against step payloads by value,
note the identity + `lc ≠ 0` (A5 diseq literal or const decide) +
the sign fact on f from the sign fact on r via the parity cases; R-h's
A5-diseq polarity convention (enters proj as `⟨6,false⟩`, the EQ atom
unnegated) to pin at the F2 seam; path-(c) keep-original tolerance;
clause-sized fuel; the kernel-decide grammar ticket needs the reducer
bridge if used. `pseudoDivisionIdentity` returns `(lc, hId)` for
exactly this consumption.

