## nla-19b Slice 1 design review `done` (2026-08-13, Danielle-requested; post-Slice-1 divergence/regret audit)

Method: adversarial re-read of the Slice-1 diff + the z3 source
re-check (:1123-1188 emission, :5095 contract), lenses: regret-later
decisions, z3 fidelity, coverage gaps.

**TWO FINDINGS (both fixed):**
- **R-a (regret, latent contamination):** `closeAlgRefl` had no
  exception restore — a `ring` throw skipped `setGoals saved`,
  leaving the tactic-state goal list polluted with the sandbox mvar
  (`closeNumericSubgoal` already restores on throw — the odd-one-out).
  Fixed: try/catch restore matching the established pattern.
- **R-b (pin gap):** no grammar pin for `r = []` (the path-(b)
  const-zero-remainder family, pd2/pd4). Added the accepting #guard.

**VERIFIED CLEAN (fidelity, with source anchors):**
- Grammar vs emission reachability: one step per replaced factor,
  independently admissible ✓; the port's release-following selectEq
  admits degree-0 (lower-stage) eqs — `pseudoDivisionCore`'s degB = 0
  branch then yields `r = []`, which the grammar's `r = []` disjunct
  admits ✓; `lcSign = 0` with non-const lc is admitted (z3's
  `sign(lc_eq)` can be 0 at the sample — the payload is a hint; the
  discharge re-proves) ✓; no `deg f ≥ k` condition (permissive —
  never genuinely emitted, but the identity still verifies and the
  transfer degenerates to a no-op; sound) ✓; const-lc `v = 0`
  admitted with `lcSign = 0` (genuinely impossible — the leading
  position of a canonical MPoly is nonzero — but permissive-and-sound) ✓.
- **The lc-assumption ↔ lemma-hypothesis correspondence (the nice
  one):** z3's A4/A5 choice is EXACTLY the sign-transfer family's
  evidence requirement: `add_lc_ineq` (the sign-pinning assumption)
  fires iff `d % 2 == 1 && !is_even && kind != EQ` (:1162-1167,
  :1181-1184) — precisely the cases where the lc's SIGN matters
  (`pdSign_odd_{pos,neg}_*`, which take `0 < L` / `L < 0`); `add_lc_diseq`
  fires otherwise — precisely the cases where only `L ≠ 0` is needed
  (`pdSign_even_*` takes only `L ≠ 0`; `pdSign_*_eq` is
  parity/sign-invariant, matching z3's EQ special-casing). The
  trusted API mirrors z3's assumption structure by construction.
- `pseudoDivisionCore (exactD=false, quotient=true)` vs the emitter's
  `(false, false)`: identical d and R; only the Q accumulation
  differs — the recomputed quotient is the right witness ✓.
- The decision-1 perturbation property is pinned (pd1 at d = 2 closes
  the same identity).
- hasMVar guards: legitimate simp/ring proofs are mvar-free; the
  guards only bite on the hole path ✓. MPolyOps (search-side
  untrusted) imported into Refute.lean (untrusted meta) — no
  trust-surface change ✓.
- Sign-transfer lemma coverage: the family's 15 members are uniform
  1-line rw-chains; the three integration pins verify the
  instantiation pattern (literal `m`, `(hL) (hE) (hId)` order) for
  one member of EACH parity family — per-parity shape risk covered;
  per-kind risk is kernel-checked text.

**Residual:** none new. Slice 2's consumption flow is the next item
(the Slice-1 entry's carried notes stand).

