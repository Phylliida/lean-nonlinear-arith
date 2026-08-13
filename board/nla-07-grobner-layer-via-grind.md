- **nla-07** `done` (2026-07-25) Gröbner layer via grind's ring engine, per
  the DESIGN §L1 decision (no PDD port). ℤ-equality goals: sandboxed fast
  path before saturation (Z3 stage-3 scheduling). All shapes: a second
  chance after the eager leaf fails, ahead of the clause tiers (their
  sign-unknown case-split cost dwarfs a failed ring probe — probe-confirmed
  heartbeat blowout the other way around). `≤`/`≥` goals additionally try
  the `le_of_eq`-strengthened form: grind's ring module derives ideal
  equalities but its cutsat bridge never consumes them (probe-confirmed on
  the equality-core inequality specimen). Attempts heartbeat-capped at half
  the remaining budget (`Core.Context` override + `tryCatchRuntimeEx`).
  Census rows division_699 + cauchy_schwarz_233 close push-button; 112
  examples green.
