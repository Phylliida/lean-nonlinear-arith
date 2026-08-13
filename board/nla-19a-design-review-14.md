## nla-19a design review 14 `done` (2026-08-10; Danielle: "is every known gap covered by a boarded item?" — R2' FIXED)

The gap-ownership audit found exactly ONE un-owned known gap: **R2'**
(review 3, APPROVED 2026-08-06 — three days BEFORE the standing
all-cases directive — as "leave + monitor, nla-16 catches"). Every
other known item was either fixed (G1–G3, R-a..R-e) or owned
(G4–G7, nla-16, F-x/F-y/F-z recorded decisions, R3' standing rule).

**R2' fixed**: `clauseStatus` reads `[l, l]`-unassigned as `.other`
(not `.unit l`), so a learned clause carrying duplicate literals
(possible in z3 — `processAntecedent` has no dedup in the mark path)
can stall UP propagation → sound rejection. Fix: `dedup` at the walk's
decide sites (`rupNode`, final bundle, native `precheck` mirror) —
`List.dedup` kernel-reduces on concrete literals (probed by `rfl`),
and `List.mem_dedup` makes it a propositional IFF, so the trusted
bridges (`clauseSatI_dedup`, `not_litSatI_forall_dedup` in
Assemble.lean) are one-liners. The returned learned-clause proof keeps
the ORIGINAL clause list's type (bridged per-proof via `Iff.mpr`).

Pin subtlety (caught while writing it): the stall requires EVERY
clause in {F ∪ units} to carry duplicates — a single non-duplicated
clause still drives propagation (e.g. `{[l,l], [¬l]}` refutes
pre-dedup since `[¬l]` is already unit). The pinned stall is
`{[l,l], [¬l,¬l]} → false` pre-dedup, `→ true` post-dedup; plus the
partial-case record.

**After review 14 there is no un-owned known gap.** What remains is
the scheduled roadmap: census slice (G4) → 19b (G5) → 12e (G6) →
Tier B (G7) → 14 (tactic) → 15 (tactus wiring) → 16 (harness, owns
G8–G10 measurement).

