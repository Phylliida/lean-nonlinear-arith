## nla-19a design review 7 `done` (2026-08-09, post-F4; Danielle-requested; boundary probes + z3 re-read)

Method: adversarial review of this session's diff (printer fix,
go3/go4/go5 dump drivers, fs1/fs2 pins) + two fresh boundary probes
(fs3: three distinct factors; fs4: `(x+1)³`) + z3-source re-read of
the eq-zero assumption path.

**VERIFIED CLEAN:**
- The fs1–fs4 dump goals are faithful nlsat inputs (unit clauses,
  stage 0, same shape as the acceptance driver).
- z3 4.12.5 factors internally for eq-zero assumptions —
  `add_zero_assumption` (nlsat_explain.cpp:261-283): `factor(p, …)`,
  collect the factors zero in the interpretation, assert one
  composite `∏ p_ij ≠ 0` atom (z3's multi-poly eq atoms). Our port's
  stage-0 refutation of fs1/fs2 with NO emitted factorSplit step is
  consistent with this architecture (factorization internal to
  explain's sign analysis); which-path byte fidelity remains pinned
  by 12c/12d.
- No new trusted-layer code this session (tests + scratch tooling
  only) — trust surface unchanged.
- The nlinarith glue is heuristic but every close is kernel-checked;
  its incompleteness is now mapped (F-v).

**F-v (REAL FINDING — checker-completeness boundary, completeness-only):
zero-product eq-implication lemmas whose required product has total
factor degree ≥ 3 exceed the F2 glue.** Empirics, all solver-refuted
at stage 0 with the same stage-0 arith-lemma shape:
- fs2 `(x-1)(x-2)=0` ∧ both `≠0`: GREEN (pairwise product).
- fs1 `(x+1)²=0` ∧ `x+1≠0`: GREEN (multiplicity 2).
- fs3 `(x-1)(x-2)(x-3)=0` ∧ all three `≠0`: REJECTED ("glue failed").
- fs4 `(x+1)³=0` ∧ `x+1≠0`: REJECTED (even multiplicity 3 fails).
The boundary is exactly nlinarith's one-round pairwise hypothesis
products (degree ≤ 2). No z3-search divergence (z3 refutes these
trivially); the gap is our checker's discharge. **Consequence for the
census slice:** the trace carries NO factorization hint for these
cores (no factorSplit step is emitted — explain keeps it internal), so
step-fact collection alone does NOT close this gap. Add to the F-iv
list: **checker-side factorization of the eq-atom poly +
`mul_ne_zero`-chain discharge for zero-product cores** (Explain's
normalizeFactorization machinery already exists to reuse; adjacent to
the already-listed multi-factor ¬EQ collapse). fs3/fs4 are pinned in
WalkTests as KNOWN-GAP expected-rejection tests — when the fix lands
the guards fail loudly and the pins flip positive.

**Regret audit:** fs1/fs2 positive pins machine-generated (printer →
paste); go5 retained in scratch_dump.lean for fs3 regeneration;
nothing else new to regret.

