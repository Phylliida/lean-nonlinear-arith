## Milestone ladder (proof-first)

- **M1** rule-correspondence spec + template lemma library built against it
  (nla-20, nla-04).
- **M2** L1 complete — bookkeeping, saturation loop, omega leaf, Gröbner
  layer; correspondence table fully covered (nla-05..07).
- **M3** quadratic-complete nlsat — degree-<=2 search + S1-free checker
  (nla-08, nla-09, nla-12 restricted, nla-19).
- **M4** S1 campaign, algebra + analysis tracks in parallel (nla-11, nla-10
  if needed).
- **M5** full checker + the containment argument written up end to end:
  per-rule fidelity (nla-20 table) + saturation completeness + RCF trace
  checking (nla-13, nla-14).
- **M6** tactus integration, then the single end-stage empirical pass:
  workspace parity harness as confirmation, not guide (nla-15, nla-16).

The guarantee is delivered by M5 on paper + kernel; M6's harness exists to
confirm budgets/performance (the one declared-empirical residue) and to catch
spec-fidelity mistakes in the correspondence table, not to define coverage.
