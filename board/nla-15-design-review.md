## nla-15 design review (2026-08-14 eve, Danielle-requested)

Divergence/regret/not-the-right-way audit of the nla-15 changes:
lean-nonlinear-arith `c7e752c` (inert-hyp skipping) + `199a57a`
(consumeMData), tactus `1cfefe16` (ladder prepend + preamble import +
path-dep require). Frame: decisions we'll regret, divergences from z3,
shortcuts.

### Findings

**R-i (REAL, probe-confirmed, fixed same-day): the strict/skip
classification order misclassified ∀-wrapped div/mod hyps.** The first
cut pre-scanned hyp types syntactically (`mentionsDivMod`) and forced
them strict — but a ∀-WRAPPED div/mod hyp (exactly vstd's div/mod
lemma shape: `∀ y, y % 2 = 0 ∨ y % 2 = 1` is a plausible
background-axiom member) never reaches its div subterm under
reifyProp (the dependent-∀ arm throws first), so the pre-scan turned
an inert hyp into a loud "dependent ∀ unsupported" failure on a
closable goal. Probe: `(hax : ∀ y : ℤ, y % 2 = 0 ∨ y % 2 = 1) (h :
x*(x+1) = 3) ⊢ False` failed pre-fix, closes post-fix. z3's spinoff
treats such facts as inert (never instantiated into nlsat's fragment).
Fixed: the pre-scan is DELETED; classification is by the reifier's own
error — `L1-owned invariant` (div/mod genuinely reached through
in-fragment structure) and `internal:` (bug visibility) rethrow,
everything else skips. The pinned top-level div/mod hyp error surface
is unchanged (byte-exact pin green). Pin added: the ∀-wrapped-div
driver, counter-pinned to L2.

### Verified clean (audit notes)

- **Skip = z3-faithful, not just convenient.** Verus's nonlinear
  spinoff query is context-free: stated requires + typ invariants +
  the assertion, no ambient axioms (Slice-0/2 recon). The
  `_tactus_bc_*` cluster is TACTUS's emission-time overlay, not
  something z3 sees — so skipping it matches z3's information state
  exactly. The arithmetically-relevant hyps (typ-invariant bounds like
  `0 ≤ a ∧ a < 2^64`, query-body assert accumulations) are all
  in-fragment and reified — verified against the walker's drop rules
  (Hyp frames dropped, requires/typ-invariants kept, body asserts
  accumulate).
- **Skip soundness under partial failure:** a mid-clausify throw can
  leave unused var/atom slots or an unconstrained bool var — never an
  unsound one (fewer constraints; the walk's precheck compares the
  table against itself; kernel re-checks all bridges).
- **Opaque-abstraction boundary:** div/mod inside an uninterpreted
  application (`f (x/2)`) is abstracted into the fresh var BEFORE the
  div is reached — the L1-owned error fires only for div/mod in
  polynomial position. Consistent with z3's nlsat view (such
  applications are fresh vars there too).
- **consumeMData coverage:** prelude (True/False goal shapes) +
  mkNnfIff (every bridge recursion) now consume; reifyProp/reifyArith
  already consumed per-recursion; the elim-plan check uses isDefEq
  (mdata-transparent). Hyp types from binders/haves are clean in
  practice; goal + hGN were the exercised (and now pinned) paths.
- **The SAT/undef exits never produce a close** — skip or no skip,
  wrong-close remains impossible (L1 sound tactics, L2 kernel-checked
  walk).
- **The inert-skip applies to the `nla_solve`/`nla_frontend` dev paths
  too** (shared prelude); all Slice-2/3/4 pins green unmodified — only
  the Slice-4 ∃ pin changed meaning (now a positive close), which was
  the point.

### Considered, not boarded

- **SAT model display is swallowed by the ladder composition.** On a
  genuinely-SAT VC, `first |` catches our model-display error and the
  user sees the scope's generic `fail "by(nonlinear_arith) scope: …"`.
  The model still surfaces when the tactic is used directly. Making
  the SAT exit ladder-transparent would take a control-flow channel
  through `first` — UX-level, not soundness; nla-16 may revisit if the
  harness shows users need the model.
- **Heartbeat blowout past `first`.** A runtime exception (both
  layers exhausting their fresh 800k budgets) is not reliably caught
  by `first |`, so the fallback arms may not run after a blowout —
  the error is loud either way, and blowout goals are beyond the
  nlinarith arms too. z3 analogue: rlimit-exceeded = unknown.
- **`TACTUS_NONLIN_NO_POOL=1` semantics shifted** — the experiment now
  measures with nonlinear_arith intercepting first. It was a July
  measurement tool; nla-16 owns proper per-arm attribution.
- **Import weight:** the preamble imports the library ROOT (all
  modules' oleans, incl. test modules). Import cost is olean-load
  only; a slim `LeanNonlinearArith.Tactic` entry point would be
  tidier but buys nothing measurable.
- **Path-dep require is non-hermetic** (`../../lean-nonlinear-arith`).
  Matches tactus's current all-local stage; switch to a pinned git
  require once lean-nonlinear-arith is pushed (noted in HANDOFF).
- **arithTyOf does not consumeMData** — type-level args of comparison
  heads carrying mdata is not known to arise; the exercised paths are
  pinned. Pin-first if it ever bites.

### Verdict

nla-15 stands with R-i fixed same-day. The round's lesson: the
skip/strict boundary is a CLASSIFICATION problem, and the right
classifier is the reifier's own error channel — a parallel syntactic
pre-scan (mentionsDivMod) was a second source of truth for the
fragment boundary, and second sources of truth drift. Same lesson
shape as Slice-3's R-i (three hand-mirrored copies of
referenced-inputs → one shared function). M6 next: the nla-16 parity
harness, which also owns measuring whether the nlinarith fallback arms
can be retired.
