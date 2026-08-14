## nla-14 Slice 3 design review (2026-08-14, build green 7615)

Divergence/regret/deferred audit of the Slice-3 code:
`Solver.checkCapturing`, `Nlsat/Quote`, the prelude/assembleRefutation
refactor, `orchestrate`, the mkAlign try-wrap, the `.le/.ge,false`
fix, and the pin infrastructure. Frame: decisions we'll regret,
divergences from z3, not-the-right-way spots.

### Findings — all fixed same-day

**R-i: the referenced-inputs collection existed in THREE hand-mirrored
copies** (`Walk.precheck`, `Walk.walkRefutation`, and Slice 3's
`Frontend.referencedInputs`). Silent drift would have meant loud false
rejections (precheck re-verifies natively — failsafe, not unsound),
but three copies of one contract is not the right way. Fixed: shared
`Walk.referencedInputCids (bundles) (final)`; all three sites rewire.
Semantics unchanged (iteration over `bundles` vs `[0:clauses.size]` is
equivalent under precheck's size check, which precedes the call).

**R-ii: two more latent bugs of the o139 class, surfaced by pinning
the uncovered arms.** The `.le/.ge,false` kernel catch was not a fluke
— it was a *coverage* failure. The audit walked the full (ck,
polarity) `mkLitIff` matrix and the reifyProp shape matrix; the gaps
each hid a real bug:

- `mkNnfIff`'s ite arms: `mkAppM ``ite_cnf #[c, a, b]` leaves the
  TRAILING `[Decidable c]` unsynthesized (mkAppM stops after the last
  explicit arg — the produced term was `∀ [inst], …`-typed and the
  bridge chain died at the next `Iff.trans`). ite hyps were broken
  since Slice 2, unpinned. Fix: `mkAppOptM` with the USER's Decidable
  instance captured from the term (a freshly synthesized one need not
  be defeq to the user's — pin the real one).
- intWits' `.nat` arm: `mkAppM ``Int.cast_natCast #[srcE]` — binders
  are `{R} [AddGroupWithOne R] (n)`; the instance can't synthesize
  with `?R` still a mvar ("failed to synthesize AddGroupWithOne ?R").
  Same for the `Nat.cast` witness. The decision-2 ℕ path was never
  exercised end-to-end (Slice-2's integrality pin was ℤ-only). Fix:
  mkAppOptM with R pinned (`Real` / `Int` respectively).

  Pins added (one driver per arm/shape — the matrix is now FULL):
  `.lt,true` (a `<` goal disproved), `.gt,true`, `.eq,true` +
  `.eq,false` (one driver), `.ge,false` (the fixed arm; o139 has
  `.le,false`), `.ne,true` (≠ hyp) + `.ne,false` (≠ goal — the
  not_not chain), Iff hyp (iff_cnf + proxies under the and), ite hyp
  (ite_cnf), and the ℕ driver (`n*n = 2`: cast links, the `0 ≤ ↑n`
  root clause, the ℕ integrality witness, B&B).

**R-iii: intBranch × non-identity reorder was unpinned.** int1/int2
have equal-degree vars → identity perm, so the permuted intWits +
`findIntegralityHyp`-at-internal-index interaction was untested. Pin:
`(y x : ℤ) (h1 : y < x) (h2 : x*x = 2)` — y registers first (deg 1),
x second (deg 2) → `reorder_lt` swaps (perm = #[1,0]) and the B&B
split on x discharges against the integrality hyp at the INTERNAL
index. Green.

### Verified clean (audit notes)

- `checkCapturing` fidelity: verbatim `check` body; `check` delegates
  (`(·.1) <$>`), so no drift channel. Perm semantics read off
  `reorder`'s remap: post-reorder `perm[internal] = external`;
  identity when `canReorder` is false (never hit at tactic level —
  frontend inputs carry no root atoms).
- cid mapping (`cid−1`): `init`'s true clause is the only
  pre-frontend clause, and the registration alignment assertion on
  total clause count catches any drift; intBranch clauses append
  mid-search AFTER all inputs and carry bundles → excluded from the
  input contract by construction; `delClause` marks, never recycles.
- Proxy patch: bvar-keyed, reorder-stable (`renameAtoms` leaves
  `.bool`; reorder never permutes bvar slots); `boolDefsOrdered`
  re-decided on the patched table (not reused).
- Quoting round-trip: precheck's `snap.atoms == goalAtoms` forces the
  quoted table to eval back exactly; any misquote fails loudly at the
  walk. `Prod.mk` nesting matches SnapshotTy's right-associated ×.
- SAT/undef arms are sound rejection only. Model display reads the
  POST-restore (external) assignment; proxy bvars carry no assignment
  (skipped by construction); refineUntilPrec 10 is a display choice.
  The undef pin documents that z3's budget check fires only after a
  BACKJUMPING resolve (stage-0 refutations bypass it — :835 shape).
- The corrupt-snapshot probe is self-checking: if the trace shape
  drifts and no proxy-carrying input antecedent exists to poison, the
  walk SUCCEEDS and the `#guard_msgs (error)` fails.
- `.ne,false` re-audited by hand: `not_not ∘ posChain` is type-correct
  (Ne reducible to Not∘Eq).

### Considered, not boarded

- Clause registration order (defClauses then roots) vs z3's
  interleaved-by-creation order: initial watch-list order divergence,
  search-side untrusted, perf-level only. Decision 1's fidelity frame
  already places proxies inside nlsat (z3's standalone mode); the
  outer-SAT-solver clause order is not the reference.
- SAT model display omits never-assigned vars and puts the ℝ-caveat
  before the model — cosmetic.
- The undef arm is pinned at the solver seam only (`maxConflicts` not
  threaded through `nla_solve`) — one-line throwError; Slice 4 may
  expose budgets if it wants.
- The o139 pin carries `maxHeartbeats 800000` — Slice 4 owns per-layer
  budgeting (`withLayerHeartbeats`); nla-16 owns the perf watch
  (mkDecideProof whnf cost on big tables).

### Verdict

Slice 3 stands. The review's real yield is the coverage lesson: THREE
latent Slice-2 bridge bugs (le/ge-false double-negation, ite trailing
instance, nat cast binder order) all sat in UNPINNED arms, and all
three failed loudly the moment a driver reached them — the
kernel-rechecks-everything architecture works. The (ck, polarity) and
reifyProp-shape matrices are now fully pinned end-to-end. Nothing
deferred; nothing divergent boarded. Next: Slice 4 (the
`nonlinear_arith` elab + L1/L2 layering + acceptance + this review's
style of audit for the layering decisions).
