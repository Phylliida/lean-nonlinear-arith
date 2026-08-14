## nla-14 Slice 4 `boarded` (2026-08-14, pre-implementation planning sweep — the `nonlinear_arith` elab + L1/L2 layering + acceptance)

Scope (nla-14-plan Slice 4 + Slice-3 close-out/review + DESIGN-endgame
§2.7): the user-facing `by nonlinear_arith` — sandboxed L1 fast path,
clean rollback to the original goal, L2 = Slice-3 `orchestrate`,
per-layer `withLayerHeartbeats` budgets, acceptance + negative probes,
stats variant, design review. **No new trusted surface**: the walk
kernel-rechecks everything L2 produces; L1 is already shipped shape.

**Interface inventory (verified against the tree at `cf3c82a`, build
green 7615, tree clean):**
- **L1 failure signaling is exception-shaped.** `saturateCore`
  (Saturate.lean:1907): early return only when `getGoals.isEmpty`
  post-ring_nf (:1911); every leaf path ends either closed or in the
  UNWRAPPED tier-2 omega (:2031) which throws; tier-1/Gröbner failures
  are caught internally and fallen through. So for the caller: normal
  return ⇒ the goal it worked on closed; any L1 failure arrives as a
  throw (tactic error at :2031 or runtime heartbeat ex). The sandbox
  idiom already exists: `tryGrobner` (:1899-1904) = saveState +
  `tryCatchRuntimeEx` + restoreState.
- **`withLayerHeartbeats` (:1862)** is the §2.7 budget primitive
  verbatim: reset init, keep user max; each layer one fresh user budget
  (Z3-per-module analogue; total ≤ layers × budget; fraction-of-
  remaining is the known-WRONG model — BUDGET-SHAPE lesson).
- **L2 is one call.** `orchestrate` (NonlinearArith.lean:1316, unsafe):
  prelude (:1174 — True-short-circuit + byContradiction + phase1) →
  register → checkCapturing → patch → bridges → walk; SAT → model
  display; undef → bounded error. It expects the ORIGINAL goal shape
  (prelude does its own byContradiction) — hence the rollback-to-
  original requirement; running it on L1's ring_nf'd, fact-noted
  context would be a different (and weaker-parity) problem.
- **Stats precedent.** `nla_saturate_stats` (:2050): resets the three
  IO-ref counters, `saturateCore (stats := true)`. The solver exposes
  `conflicts`/`maxConflicts` (Solver.lean:126/129, default UINT_MAX =
  nlsat_params default).
- Root import + test file already in place
  (LeanNonlinearArith.lean:70-71).

### Decisions — RESOLVED (Danielle's standing principles 1–4, this session)

- **D1: the dev elabs `nla_frontend`/`nla_solve` STAY.** They carry the
  Slice-2/3 pin matrix; deleting them would churn the very pins that
  guard the layering (principle 2). The user surface gains
  `nonlinear_arith`; the dev entries stay documented as dev entries.
- **D2: `nonlinear_arith (n)?` — yes, mirroring `nla_saturate (n)?`.**
  The numeral forwards to L1's `maxRounds` only; the default stays
  depth-adaptive so default behavior is untouched (principles 1/4 —
  z3-internal scheduling knobs exist too; surface parity holds at the
  default — and 3: the plumbing is one argument).
- **D3: no `maxConflicts` threading through the tactic.** z3's own
  default IS UINT_MAX (Solver.lean:129 comment = nlsat_params default),
  so the faithful surface keeps the field at default; the user-level
  budget is `maxHeartbeats` (the z3-rlimit analogue), already per-layer
  via `withLayerHeartbeats`. The undef arm stays pinned at the solver
  seam. (Resolves the Slice-3 review's "considered, not boarded" item
  by principle 4: in z3 that knob exists only as a non-default param.)

### The elab (the whole new surface — none of it trusted)

```
elab "nonlinear_arith" n:(num)? : tactic => unsafe do
  let g0 ← getMainGoal
  let s ← saveState
  let l1 ← tryCatchRuntimeEx
    (do withLayerHeartbeats (saturateCore (maxRounds := n.map (·.getNat)))
        unless ← g0.isAssigned do
          throwError "nonlinear_arith: internal: L1 returned without closing"
        pure true)
    (fun _ => do restoreState s; pure false)
  unless l1 do withLayerHeartbeats orchestrate
```

Edge case, considered-not-engineered: `ring_nf at *` can close g0
outright, after which saturateCore works on the NEXT goal; if it throws
there, the rollback resurrects g0 and L2 closes it via the walk —
correct, at worst redundant. saturateCore is goal-agnostic by design;
pin the behavior only if a driver ever hits it.

### Work items, in order

1. **The elab** (above) at the tail of `Tactic/NonlinearArith.lean`,
   next to `nla_solve`. ~25 lines. `unsafe` is transitive (orchestrate
   → walkRefutation → evalExpr); tests calling it are unsafe too.
2. **`nonlinear_arith_stats`** mirroring `nla_saturate_stats`: reset
   the counters, run L1 with `stats := true`, report WHICH LAYER
   closed; on L2 also report the solver's `conflicts` from the final
   state. Mechanism: an IO-ref (`nlaL2Runs` counter + conflicts
   snapshot) set inside `orchestrate`, mirroring the `nlaTacticCall`
   pattern (Saturate.lean:851) — this ref doubles as the
   L1-never-touches-L2 pin mechanism. Orchestrate otherwise UNTOUCHED.
3. **Pins** (NonlinearArithTests, new `Tests.NonlinearArith` section):
   - **L1-never-touches-L2**: a saturate-closable goal through
     `nonlinear_arith`; assert via the L2-run counter that orchestrate
     was never entered.
   - **Layered L2 acceptance**: the o139 census goal in user syntax,
     end-to-end. `set_option maxHeartbeats 800000` moves ONTO THE TEST
     (Slice 4 owns the budgeting — each layer gets the fresh user
     budget; L1's failure must roll back clean).
   - **Per-driver layer probe, then pin the ACTUAL layer**: the Slice-3
     drivers (sq/disj/proxy/int1/int2/reorder/intBranch×reorder)
     re-run through the layered entry — several may close in L1 now
     (that's the layering working). Probe first, pin what each driver
     really does (standing lesson: probe before assuming).
   - **Negative probes through the layering**: genuine-SAT goal →
     model-display error, never a wrong close; a div/mod goal L1 can't
     close → the reify-boundary hard fail (re-pin of the Slice-3
     surface); unhandled hyp/goal shape → loud reify error
     (corrupted-context rejection — never a silent drop).
   - One disjunctive/proxy driver through the layering (decision-1
     Boolean surface, plan acceptance).
   - undef stays pinned at the `nla_solve` seam (D3); re-pin through
     the layering only if the surface differs — expected identical.
   - The whole existing suite (SaturateTests, NonlinearArithTests
     Slice-2/3 pins, WalkTests…) stays green UNMODIFIED — the elab is
     new code.
4. **Acceptance sweep** (nla-14-plan, all in user syntax via
   `by nonlinear_arith`): sq/xl-class ℝ drivers, int1/int2-class ℤ
   drivers through the 12e B&B path, the ℕ driver, o139; layering +
   budget pins above; full Boolean structure in hyps/goal; negative
   probes above.
5. **Close-out**: design review (Danielle — the Slice-3
   divergence/regret frame, this time on the layering: rollback
   fidelity, budget shape, per-driver layer assignment), board
   close-out, HANDOFF rewrite, memory append. nla-14 then `done`.

### Traps carried forward

- `tryCatchRuntimeEx`, not plain `catch` — heartbeat blowout is a
  runtime ex (tryGrobner precedent).
- The Slice-5 env-keeping lesson does NOT apply to the L1→L2 rollback
  (no proofs are extracted from a FAILED L1), but the restore must be
  the FULL pre-L1 state: L1's noted-fact env/context additions must not
  leak into L2's prelude.
- Do NOT shrink L2's budget "because L1 already spent some" — that is
  the fraction-of-remaining anti-pattern; each layer is its own fresh
  scope (BUDGET-SHAPE lesson, withLayerHeartbeats docstring).
- mkDecideProof whnf on big tables is o139's 800k — nla-16 owns the
  perf watch, not this slice.

### Estimate + roadmap (unchanged)

Slice 4 ≈ 1 session (elab glue + pins; zero new trusted components).
Then nla-14 `done` → nla-15 (tactus wiring, ½) → nla-16 (parity
harness; owns G8/G9/G10 + the R-iii probes + the mk_ineq_atom
normalization gap + glue-subsumption watch) = M6. Q7 open: re-offer 11a
(resultants) as the interleave lane.

---

## Close-out (2026-08-14, same day) — LANDED, build green 7615

**Landed as planned.** `Tactic/NonlinearArith.lean` gains the Saturate
import (acyclic — Saturate imports Templates/Oracle only), the
`nlaL2Runs`/`nlaL2Conflicts` refs (bumped inside `orchestrate` — its
only change), `nonlinearArithCore` (the §2.7 layering: saveState →
tryCatchRuntimeEx(withLayerHeartbeats saturateCore + g0.isAssigned
check) → on failure full restoreState + withLayerHeartbeats
orchestrate), and the `nonlinear_arith (n)?` / `nonlinear_arith_stats
(n)?` elabs (D2: the numeral forwards to L1's maxRounds only). No
existing pin touched; full build green 7615.

**Probe-verified layer assignments (scratch_layerprobe.lean):** int1,
int2, AND the R-iii driver close in L1 (the mined `x*x = 2`
down-propagates to |x| ≤ 1 and the corner refutation fires — no B&B
needed); the ℝ drivers, the ℕ driver, and o139 fall to L2. The
probe-first rule caught a real coverage hole in the plan: the planned
"int1/int2 through the 12e B&B path" acceptance would have been a
no-op. It is carried instead by the NEW driver `x*(x+1) = 3` (real
root (−1+√13)/2, no integer one; L1 bounds x only one-sidedly from the
equation) plus its two-variable reorder variant (perm = #[1,0],
intBranch discharging at the internal index — the R-iii interaction
through the layering).

**Pins (Tests.NonlinearArith):** L1-never-touches-L2 (run_cmd counter
sandwich), tangent specimen with the round numeral, int1-L1, sq-L2 +
the byte-exact `nonlinear_arith_stats` layer line (4 conflicts — L1
throws before its stats print, so the layer line is the only info
message), the disj/proxy/int2/reorder/ℕ acceptance sweep, both B&B
drivers, o139 end-to-end through the layering (budget on the test,
fresh per layer), the True short-circuit, the SAT model display and
div/mod hard-fail byte-identical to their nla_solve surfaces, and the
new unsupported-hyp-shape rejection (an ∃ hyp — loud, never a silent
drop).

**Catches worth the books:**
- **run_cmd counter sandwiches** are the pin mechanism for
  tactic-internal state: IO.Ref instrumentation set inside the tactic,
  reset/read by `run_cmd` around the example — deterministic because
  command elaboration is sequential. (`#guard_msgs` can't pin L1's
  stats line — it carries wall-clock ms.)
- **Probe before pinning layers** (the standing lesson, again): two of
  the plan's assumed-L2 drivers turned out L1-closable; asserting the
  planned layer would have silently DELETED the B&B acceptance
  coverage.
- The registration-order hyp (`y < x` in the reorder drivers) is
  genuinely unused by the refutation — the unused-variable lint is
  correct and the hyp is load-bearing meta-structure; suppress with a
  comment saying why.
- `nonlinear_arith_stats` resets ALL counters at entry (mirrors
  `nla_saturate_stats`) — counter pins must set-then-run, never rely
  on values across a stats call.

**Next:** Slice-4 design review (Danielle — the divergence/regret
frame on the layering: rollback fidelity, budget shape, per-driver
layer assignment), then nla-14 `done` → nla-15 (tactus wiring).
