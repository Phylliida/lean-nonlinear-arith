## nla-19b Slice 3 design review `done` (2026-08-13, post-Slice-3; divergence/regret audit of the gate lift + pd1 walk)

Danielle-requested audit of the day's work (commits `52ee0f8`,
`09a75b0`, `2b6116e`, `33b2f18`): the isV0/nodeFSet gate lift, the pd1
WalkTests section, and the close-out docs.

### Verified clean

- **F-set completeness vs z3's lemma structure.** pd steps contributing
  nothing to `nodeFSet`/`buildFSet` is not a divergence: in z3,
  `simplify(literal,…)`'s pseudoDivision emission justifies the arith
  lemma — every literal z3 adds to the learned clause (the rebuilt
  literal, the A4/A5 lc assumptions) lives in our `.resolution (.arith
  …)` marker's clause value, never in step payloads. The RUP skeleton
  (`resolution` markers) mirrors z3's resolution structure; pd steps
  are explain-internal in z3 too, invisible to the propositional DAG.
- **S1 interplay.** `inFragment` is degree-neutral for pd by design
  (Trace.lean:169-174 documents exactly this: ring identities are
  degree-generic), and the Slice-1 discharge is degree-generic (`ring`
  closes any per-instance identity). No hidden degree gate introduced
  by the lift.
- **No masked pins.** `pseudoDivision` appears in WalkTests only in the
  new pd1 section — no pre-existing negative probe relied on the isV0
  reject (green build pre-lift already implied this; confirmed by
  grep). The 30 Refute-level pd pins reject at the discharge lane, not
  at isV0 (`nlsat_arith_valid_steps` doesn't run `precheck`).
- **Grammar reachability.** Post-lift, `precheck`'s order (isV0 then
  `grammarOK`) makes the grammar gate a pd bundle's first line — the
  lcSign=2 probe pins exactly this path (pre-lift it was masked).
- **Precheck rejection path for intBranch** still verified by the
  native guard (bundle with `.intBranch 0 (1/2 : Rat)` → `isV0 ==
  false`).

### Findings fixed same-day

- **R-i (doc):** `nodeFSet`'s docstring still listed "non-v0 step" as a
  live error without noting it is now intBranch-only and unreachable in
  practice (`precheck`'s isV0 gate fires first — the throw is dead-code
  defense, matching `buildFSet`'s documented pattern). Fixed.
- **R-ii (nit):** the intBranch gate guard used witness value `0` — an
  INTEGER value z3 would never branch on (branching happens at
  non-integer witnesses). Gate-only test so semantics were irrelevant,
  but realism is free: now `(1/2 : Rat)`.

### Boarded (were unboarded)

- **R-iii → boarded (nla-16 lane): pd-driver z3-binary differential
  probe.** o139 was validated against the real z3-4.12.5 build (exact
  6-conflict count, G11 session); the pd drivers (pd1/pd2/pd3/pd4/pd6)
  are anchored to SOURCE READING only — their payloads matched the
  expectations derived from nlsat_explain.cpp:1096-1216, but no
  differential run against the binary (`/tmp/z3-4.12.5`, `make -j
  shell`) pins conflict counts / emitted payloads. Search-side
  (untrusted) so soundness is untouched, but the standing directive is
  fidelity. Cheap: five driver inputs through the z3 shell with nlsat
  statistics, compare against the WalkTests/RefuteTests snapshots.
- **R-iv → boarded (12e): intBranch grammar condition.** `grammarOK`'s
  intBranch arm is unconditionally `true` (Trace.lean:370-371;
  verified by native guard). When 12e lifts the isV0/nodeFSet gate,
  the grammar gate becomes an intBranch bundle's first line — and it
  currently admits everything, including integer `v` (z3 branches only
  at NON-integer witnesses). `v` non-integer is decide-grade
  (`v.den ≠ 1`) and belongs in the grammar per the Slice-1 structural-
  conditions pattern; the witness-consistency of `v` with the sample
  stays discharge-side. Note added to HANDOFF's 12e section.

### Considered, not boarded (with reasons)

- **Walk-level snapshots for pd2/pd3/pd4/pd6.** Only pd1 is walked;
  the other four drivers have Refute-level pins with firing
  confirmations (Slice 2). Walk-level adds only precheck/RUP/DAG
  coverage, which pd1 exercises identically; the per-driver
  differences (A4 lc-ineq, kind flip, even-d, const-drop) live in the
  Refute lane. Regeneration is cheap (`scratch_dump.lean` prints all
  four) — pull forward if nla-16's harness ever shows a walk-level
  lane difference; until then redundant.
- **Walk-level firing witness.** The positive pd1 walk does not prove
  the transport FIRES (glue-subsumption closes it step-free — the
  Slice-2 finding). Firing is pinned at Refute level (instrumented
  confirmations + hint-flip pins in Slice 2). Making pd1's walk
  transport-load-bearing would require crippling the glue — backwards.
  Already watched at nla-16 (glue-subsumption note, Slice-2 board).
- **Explicit `.pseudoDivision => pure ()` arm in `nodeFSet`** instead
  of the catch-all: the catch-all already silently accepts six other
  step shapes (projection steps, factorSplit); an explicit arm for one
  of seven adds noise, and the comment above the arm documents the pd
  case. Left as-is.
- **`isV0` name drift** ("v0" now includes pseudoDivision): a rename
  (`isCheckable`) churns every reference for a naming nicety; the
  docstring rewrite carries the meaning. Left as-is.
- **Walk.lean:331 unused-variable warning (`atomsV`):** pre-existing
  (verified against the pre-lift tree), cosmetic, out of Slice-3
  scope.
