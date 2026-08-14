## nla-15 `done` (2026-08-14) — tactus closer wiring: emit `nonlinear_arith` for
`by(nonlinear_arith)` sites. Toolchain already aligned (tactus/lean-project
pins lean+mathlib v4.25.0, identical to ours; integration is a require line).

### What landed

**tactus side** (repo `verus-cad/tactus`):
- `lean-project/lakefile.lean`: `require LeanNonlinearArith from
  "../../lean-nonlinear-arith"` (path dep; `lake update` recorded in
  the manifest). lean-project is THE package every per-fn/pkg Lean
  invocation runs in (`lake env printenv LEAN_PATH` per the check.sh
  convention), so the one require covers all crates.
- `tactic_select.rs` `nonlin_ladder`: `nonlinear_arith` is the FIRST
  arm of the per-goal nonlinear ladder (`first | nonlinear_arith |
  <pool arm> | <R1–R4 computed arms> | <denom-positivity>`). The
  heuristic arms stay as fallback — definition-unfolding shapes
  (denominator positivity) are definitionally invisible to any
  arithmetic tactic; nla-16 owns measuring which arm closes what.
- `sst_to_lean.rs` `nonlinear_preamble_fragments`: +=
  `import LeanNonlinearArith` (alongside `Mathlib.Tactic.Linarith`,
  which the fallback arms still use).

**lean-nonlinear-arith side** (two behavior changes the wiring forced):
- **Inert-hyp skipping (phase1).** Every tactus proof context carries
  the `_tactus_bc_*` ambient-axiom haves (dependent ∀s) — a strict
  reify would throw on every real goal and the wiring would be a
  no-op. Hyps outside the arithmetic fragment (dependent ∀, ∃,
  unsupported-type comparisons, prop applications) are now SKIPPED +
  counted; the negated goal and div/mod hyps stay STRICT;
  `internal:`-prefixed errors rethrow. Parity argument: the spinoff
  query carries those facts too and nlsat never consumes them (MBQI
  off) — skipping is sound weakening, and z3-faithful. The SAT-exit
  message discloses the skip count. The Slice-4 ∃-hyp pin flips to
  positive; new pins: inert-skip closure, SAT-skip-note (byte-exact),
  strict-goal rejection.
- **mdata robustness (kernel-caught by the fixture gate).** A
  preceding `have` wraps the goal in `noImplicitLambda` mdata:
  prelude's `isConstOf ``True`` short-circuit missed, and the mdata
  leaked into hGN's type, where mkNnfIff (no consumeMData) skipped the
  True/False arms and the catch-all ascribed `Iff.refl ¬True` where
  `not_true` was needed — the FINAL KERNEL CHECK rejected the term
  (`id (Iff.refl ¬True)` vs `(¬True ↔ False) → …`). Comparisons
  survived because mdata is defeq-transparent; only the True/False
  leaves have genuinely different sides — which is why every pin
  passed until the fixture's degenerate `True` theorem. Both sites now
  `consumeMData`. Pins: have-then-True (the fixture's exact shape),
  mdata-wrapped real goal, the `.fls` empty-clause root (`(h : ¬True)
  ⊢ False`), `¬¬True`.

### Gate results

- **Decisive probe** (`bootstrap-fixture/nla15_probe.rs`): o139 over
  `int` — the transitivity-of-fractions census shape; nlinarith
  structurally cannot close it (no eq kernels for R3/R4; the pool arm
  caps degree-3 cross products). **1 verified, 0 errors** — the
  `nonlinear_arith` arm carried it. Re-run green after the mdata fix.
- **Fixture regression** (`bootstrap-fixture/lib.rs`): 24 verified /
  10 errors with the old binary = 24/10 with the new — all
  pre-existing fixture rot (incl. the known-red fill_zeros; the
  fixture's canonical command references a removed flag, so it hasn't
  been kept green). The new arm's one initial regression (the kernel
  mismatch above) is fixed; direct `lean` elaboration of the
  regenerated pkg module confirms 0 kernel errors.

### Traps worth the books

- The stmt-olean / per-fn builds bypass lake when LEAN_PATH is set —
  the crate-local check.sh convention exports `LEAN_PATH="$(cd
  tactus/lean-project && lake env printenv LEAN_PATH)"`; running verus
  without it fails with "unknown module prefix 'Mathlib'" — not a
  regression, a missing env.
- `--lean-all-proofs` no longer exists (probe headers referencing it
  are stale); `--tactus-package-check` is the default under
  `--lean-backend` since M6.5.
- `lake build` in lean-project fails on the missing `TactusCheck.lean`
  root — PRE-EXISTING (the package is env-only; verus uses `lake env
  lean`, never builds the default target).
- Path-dep oleans load fine against lean-project's own mathlib
  checkout (same v4.25.0 pin) — verified by direct elaboration.
- The kernel error position points at the DECLARATION header, not the
  failing subterm — reproduce by running `lean` on the emitted pkg
  file directly (emission always runs, even on verification failure).
