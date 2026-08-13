## nla-19a design review 6 `done` (2026-08-09, post-F3; Danielle-requested; probes + adversarial re-read)

Method: adversarial re-read of `Walk.lean` + the Assemble.lean
additions against the review-4 R-iv/R-v/R-vi recipe and the two live
dumps, plus three fresh probes for precheck branches the pin suite
doesn't exercise. Lenses: regret-later decisions, z3 fidelity.

**VERIFIED CLEAN (probes):**
- **P1 (atom-table gate):** snapshot atoms ≠ goal atoms rejects with
  "atom table mismatch (goal vs snapshot)" — the V-fidelity check works.
- **P2 (forward reference):** a bundle referencing a later learned cid
  rejects with "forward reference to learned clause". (Creation order
  makes this dead on real traces; the gate is the sound direction.)
- **P3 (duplicate antecedents):** accepted — RUP is duplicate-
  insensitive; permissiveness confirmed, not just rejection paths.

**VERIFIED CLEAN (re-read):**
- `.decision` skip: decision literals stay IN the learned lemma (z3
  resolve keeps them; they are not antecedents) — skipping them in the
  F-set is exactly right.
- `upRefutes` fuel: `sz + 1` with each propagation assigning one
  FRESH bvar (unit literal is `.un` by definition) — always sufficient.
- Deleted clauses are checker-irrelevant: bundles capture lemmas at
  flush time; `delClause` post-dates the flush.
- `arithClauseVal` = `proj ++ ¬core` mirrors `arithClause` (V-i of
  review 4) — pinned by every green test.
- A learned bundle with an empty lemma is handled soundly (the derived
  `clauseSatI I []` is reachable only when the F-set is genuinely
  unsatisfiable — byContradiction + RUP).

**FINDINGS (all recorded, none blocking F4):**
- **F-w (the real one): the R4' negative probes are partially
  INAPPLICABLE post-review-5.** The old F4 plan's "corrupted `mkNeg` /
  corrupted `sp`" probes assumed the checker parses step payloads. It
  does not: the walk re-discharges arith lemmas from the clause
  literals alone, so payload corruption that leaves the emitted arith
  clause intact is INVISIBLE to F3. This is SOUND (accept-⊆-valid
  holds: every accepted refutation has kernel-checked arith lemmas +
  RUP chain), but two consequences: (a) the contract is precisely "the
  checker accepts a SUPERSET of grammar-admitted traces — those whose
  arith lemmas it can independently re-discharge"; grammar membership
  guides completeness (census slice), never soundness; (b) the
  mkNeg/sp corruption probes move to the census slice (which consumes
  payloads via `extractFact`/Coverage). If a grammar LINT is wanted as
  a fidelity gate, it needs a decidable `grammarOK : TraceStep → Bool`
  mirroring `TraceStep.Grammar` — cheap, and the census slice needs
  the shape classification anyway. Deferred there.
- **F-x (tech debt, completeness-only): duplicated F-set logic** —
  pure `nodeFSet` (precheck) vs meta `buildFSet` (term construction).
  Drift fails SAFE (precheck-pass + walk-diverge ⇒ the kernel `decide`
  on the walk's values fails ⇒ rejection; precheck-fail ⇒ rejection).
  Unification available: precheck returns per-node F-sets for
  `buildFSet` to consume. Not done — the duplication is 20 lines.
- **F-y (contract rigidity, for nla-14):** `Cs` must be EXACTLY the
  referenced input clauses in cid order. R-vi assigns goal-atom/clause
  alignment to 14 (it replays the same init), so strictness is fine
  and gives loud failures; if 14 finds it awkward (extra ambient
  hypotheses), relax to subset-lookup — `memChain` is position-based,
  a find-based variant is easy. Keep strict until then.
- **F-z (cosmetic):** no `clauses[cid].learned` consistency check —
  a bundle at an input clause's cid would be processed as learned (V1
  still pins lemma = lits). Sound; noted, not worth a gate.

**z3-fidelity verdict:** F3 has no z3 counterpart by design (R-viii —
z3 trusts its search). The one completeness-critical assumption —
z3's trail-scan resolution chains are RUP-derivable from the recorded
antecedents (reverse of a resolution chain is a RUP chain) — stands,
now exercised by both live refutations end-to-end; nla-16 is the
empirical backstop, the census slice the systematic one. No new
divergences found; the divergence register is untouched.

