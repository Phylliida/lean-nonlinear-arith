# DESIGN — discharge oracle: tryDischarge hygiene, mineBounds completeness, call scaling

Follow-up plan from the 2026-07-24 review of `Tactic/Saturate.lean`. Three
items; the last two converge on one architectural answer.

## 1. Canonical tryDischarge (small, do first, fresh session)

Current: save state, run `assumption <|> omega` on a fresh mvar, restore on
failure only — on success, omega's metavariable-context growth and info trees
persist in the session state.

Canonical pattern: sandbox *both* paths. Run the tactic, extract the **fully
instantiated proof term inside the sandbox**, then roll everything back and
return the term:

```
def tryDischarge (ty : Expr) : TacticM (Option Expr) := do
  let s ← saveState
  try
    let mvar ← mkFreshExprMVar ty
    let gs ← Lean.Elab.runTactic mvar.mvarId! (← `(tactic| first | assumption | omega))
    if gs.1.isEmpty then
      let pf ← instantiateMVars mvar
      restoreState s
      -- pf must be closed: guard `!pf.hasExprMVar` (assumption/omega produce
      -- closed terms; the guard turns a silent soundness-adjacent surprise
      -- into a loud skip)
      if pf.hasExprMVar then return none
      return some pf
    else restoreState s; return none
  catch _ => restoreState s; return none
```

The extracted term is self-contained data; rolling back the assignment does
not invalidate it. Add the `hasExprMVar` guard — that is the one failure mode
of the extract-then-rollback pattern.

## 2. mineBounds completeness

Two distinct miss classes, different answers:

**(a) Syntactic misses of literal bounds** (`c ≤ f` present in hyps but the
factor expr differs by mdata/instance noise from the collected monomial
factor). Post-`ring_nf at *` both sides are canonized, so structural `==` is
already near-complete for this class. Residual fix, cheap: compare
`Expr.consumeMData` on both sides (and mine after `instantiateMVars` on hyp
types). Not worth more machinery than that.

**(b) Derived bounds that never appear syntactically** — e.g. from
`a ≤ b - 2` and `5 ≤ a`, the bound `7 ≤ b` is implied but written nowhere,
so the miner never anchors a tangent plane at 7. Syntactic mining is
*structurally* incomplete here; per-candidate omega probing (binary search
per atom, ~64 calls/direction) is complete but multiplies the call-scaling
problem. This class is properly solved by item 3's oracle, not by a smarter
miner.

**Non-goal:** symbolic (variable-to-variable) anchors. Tangent/order
conclusions stay linear only with literal anchors; Z3 gets its literals from
the model. Symbolic-bound generation is model-guided v1 territory (nla-06),
not a mining bug.

## 3. Discharge-call scaling

Cost model today: every premise attempt is a full omega elaboration
(~5–15 ms). Per goal: monomials M × (sign rules ~16 premise attempts +
order/corner/tangent ~4 combos × |bounds|² × 2). Realistic Verus goal
(M ≈ 10, 2 mined bounds/factor): **~600 omega calls ≈ 5–10 s. Unacceptable.**

**v0.5 — cheap restructuring, no new trust surface (do soon):**
1. **Memoize** tryDischarge on the premise type (`Expr` key, cache invalidated
   per generation round): `0 ≤ a` is currently re-proved by every rule that
   wants it.
2. **Per-factor sign lattice, computed once**: for each distinct factor,
   determine its position in {pos, nonneg, zero, nonpos, neg, unknown} with
   ≤ 2–3 discharge calls, *then* instantiate all sign/pow rules from the
   lattice with zero further calls. Kills the per-rule × per-premise blowup.
3. **Literal side conditions bypass omega**: `0 ≤ 2`, `Even 2`, `2 ≠ 0` are
   decided in meta code (Int compare / parity on the literal) — currently some
   go through full tactic calls.
   Estimated result: ~600 → ~25 calls/goal, well under any closer budget.

**v1 — the real fix, folds into nla-06:** an **untrusted linear oracle**
(exact-rational Fourier–Motzkin or simplex over the atomized hypotheses,
~300 lines of meta code) that in ONE pass computes: tightest implied literal
bounds per atom (solves 2b), the sign lattice, and infeasibility with Farkas
certificates. Generation then reads the oracle's table and makes **zero**
trusted calls; trust stays at the leaf (omega) plus per-certificate
`linear_combination` checks. This is the same component nla-06 v1 wants for
model-guided anchor selection, so it is one investment serving three needs:
completeness (2b), scaling (3), and Z3-parity model guidance (nla-06).

Sequencing recommendation: 1 and v0.5 next session (contained, ~a morning);
v1 when nla-06 opens or when the parity harness shows v0.5 isn't enough.

## Outcome (2026-07-24, implemented)

Items 1, 2a, and v0.5 landed. Measured on the §3 cost-model stress goal
(8 monomials, lb+ub per factor): baseline **timed out** at the default
heartbeat budget; now **~2.1s total** (generate 1.8s · 32 tactic calls ·
162 cache hits · 23 literal fast-paths · omega leaf 76ms). The ~600→~25
call estimate was accurate (32 actual). `nla_saturate_stats` reports phase
timings and oracle counters.

Two assumptions in this document were wrong, both found by the stress goal:

1. **"The extracted term is self-contained data" — false in the environment
   dimension.** omega can mint auxiliary env constants (`_example._proof_N`)
   that the extracted proof references; full rollback deletes them and the
   kernel rejects the final proof. Fix: keep the post-tactic *environment*
   (monotone, benign) while restoring the rest of the state
   (`let env ← getEnv; restoreState s; setEnv env`). The `hasExprMVar` guard
   stays for the metavariable dimension.

2. **The proof's syntactic type is not the probed type.** `assumption`
   closes `0 < a` with `ha : 1 ≤ a` by ℤ defeq (`Int.lt` unfolds to `+1 ≤`),
   so meta-level weakenings (`le_of_lt` on a lattice fact) failed to unify.
   Fix: ascribe the probed type with `mkExpectedTypeHint` on extraction.

And one bottleneck this document missed entirely, dwarfing the call-count
problem: **noted facts containing `min`/`max` (the corner bounds) make the
omega leaf case-split per occurrence** — exponential in the number of corner
facts (measured 168s leaf; they also poisoned every later premise-discharge
omega, 5.4s generate). Fix: fold the corner `min`/`max` to a single literal
at generation time (`le_trans` with a `decide`d literal comparison). Design
rule going forward: **never note a fact whose statement contains `min`,
`max`, `if`, or any other case-splitting connective** — resolve them in meta
code where the values are literals.
