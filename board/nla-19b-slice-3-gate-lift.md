## nla-19b Slice 3 `done` (2026-08-13) — isV0 gate lift + pd1 acceptance → **M3**

The final 19b slice (spec: `nla-19b-plan.md` Slice 3). With o139 walked
in the G11 session, pd1's walk completes the acceptance pair:
**M3 (quadratic-complete nlsat — degree-≤2 search + S1-free checker) is
declared** per the milestone ladder and DESIGN-endgame §2.5.

**Gate lift (commits `09a75b0`, `2b6116e`):** `Trace.lean` `isV0` drops
`.pseudoDivision` from the reject set (`.intBranch` stays gated → 12e);
`Walk.lean` `nodeFSet` passes pd steps through with no clause-level
facts (same treatment as projection steps, review-5 F-i — they are
step-facts consumed checker-side by `Refute.collectStepFacts`);
`buildFSet` already forwarded them via `priorSteps` — no change needed.
The lift is WITNESSED, not blind: emission shapes per acceptance driver
were pinned in the Slice-2 census table before lifting.

**Acceptance (WalkTests):** machine-generated pd1 snapshot
(`scratch_dump.lean` `goPd1`, regenerated post-lift): the solver learns
`x0² < 0` (atom 3, the path-(e) rebuilt literal) off
`pseudoDivision x1 (x1−x0²) 1 1 x0² 1 false` — exactly the
Slice-0-pinned payload — then the final bundle's `leafNumeric` kills
it. Walked from both input clauses end-to-end.

**Pins (F-w pattern):**
- gate guards (native): pd1 learned bundle `isV0 == true`;
  `intBranch` bundle `isV0 == false`;
- step-free variant closes (glue-subsumption at walk level — the
  RefuteTests pins cover the Refute level);
- corrupt-R variant (grammar-clean — r = x0²+1 has degIn x1 = 0 < 1 —
  identity false) → `pseudoDivisionIdentity` throws, step skipped
  soundly, walk still closes on the glue (corrupted payloads degrade,
  never unsound);
- grammar-bad variant (lcSign = 2) → precheck reject. Pre-lift this
  was masked by the isV0 reject firing first; post-lift the grammar
  gate is a pd bundle's first line of defense.

**Trap for the books:** a doc comment (`/-- -/`) directly above
`#guard` fails parsing with "unexpected token '#guard'; expected
'lemma'" — docstrings attach only to declarations, and `#guard` is not
in the post-docstring command first-set. Use `/- -/` for guard pins.

**Close-out:** G5 row flipped in the gap inventory; M3 declared.
Next per the roadmap: 12e (G6, integer B&B — where the leftover
`intBranch` gate lifts) → nla-14 → nla-15 → nla-16 = M6.
