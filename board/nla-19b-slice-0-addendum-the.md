## nla-19b Slice 0 addendum (2026-08-10 eve): the o139 divergence RESOLVED — `Explain.project` todo writeback bug

**Root cause (REAL port bug, first live fidelity bug found by
recon):** `Explain.project`'s while-loop called
`removeMaxPolys` and assigned the rest only to a local mutation
variable — the STATE's `todo` never lost the processed polys (the
pre-loop call writes back; the in-loop one at :591 did not). z3 has
no writeback to mirror: `remove_max_polys` MUTATES `m_todo` in place
(`git show z3-4.12.5:src/nlsat/nlsat_explain.cpp:1011`); the
functionalization omitted the store. Effect: once any loop iteration
INSERTS a projection poly (bilinear psc resultants do this: the
o139 first conflict's inserted `x0·x2·x4 − x1·x2·x3`, carrier of the
bug), the state todo permanently re-contains it, `maxVar` stops
descending, and the loop re-processes the same poly set forever —
re-emitting its cell literals, 150k+ iterations observed in 2 min.
The "60-minute search divergence" was ONE explain call trapped in
`project`.

**Why every pin and review missed it:** the `if (← get).todo.empty
then break` check reads the STATE todo — and the pre-loop writeback
empties it whenever the projection set is small, so the buggy in-loop
call is only REACHED when a projection inserts new polys mid-loop.
No prior driver (≤ 2-projection-poly cores, small chains) ever did;
ordering_139's bilinear resultants are the first insertion-heavy
projection in the exercised corpus. A textbook coverage-shape
survivor, not an analysis failure.

**Fix (2 lines, Explain.lean):** write `todo'` back to state after the
in-loop `removeMaxPolys`; mirror z3's `m_todo.reset()` on the
`all_univ` break (:1002-1005). Sibling-site audit: `removeMaxPolys`
has exactly two call sites (both in `project`); no other
functionalized-mutation skeleton in `Explain`/`Solver` has this shape
(`simplifyCore`/`normalizeCore` thread their state correctly).

**Post-fix behavior:** o139 refutes end-to-end in 13–45ms with the
production explain — **6 conflicts, exactly z3-4.12.5's count**
(z3-4.12.5 built from the audited checkout this session: unsat, 28ms,
6 conflicts/11 propagations/7 stages; 4.16 classic-config identical).
ZERO snapshot churn: full build green 7612 jobs, every WalkTests/
ExplainTests/Solver/Refute pin re-green — consistent with the
analysis (drivers that completed never reached the in-loop call, so
the bug was latent on all pinned workloads). **Every o139 trace bundle is
isV0=true ∧ isS1Gated=false** (its one rootGeneric step is deg ≤ 2,
fragment-passing, and the bundles carry no pseudoDivision/intBranch)
— **o139's full refutation is v0-walkable TODAY**, restoring it as a
candidate M3 acceptance driver (6 vars, 6 conflicts, 12 clauses,
rootGeneric + cellBound + linearRoot + factorSplit shapes; the
richest real DAG we have).

**Methodology notes worth keeping:** the bisect chain that isolated it
in ~1 hour: mockExplain swap (search fast ⇒ explain is the hog, not
search dynamics) → capped-conflict timing (>280s INSIDE one explain
call) → temporary `dbgTrace` journal in `project` (todo×3 cycling at
x=4 — instrumentation reverted immediately, never committed) →
todo_set source re-read (z3's in_set is current-contents-only,
killing the sticky-dedup red herring) → writeback omission by
line-comparison. Danielle's call to reason from source was the
decisive steer; the empirical work's role was localization. z3
4.12.5 local build: worktree at /tmp/z3-4.12.5 (Git worktree off the
audited checkout; `make -j shell`; keep for future differential
probes). Regression pin: `ExplainTests` ordering_139 end-to-end
(`r == some .false ∧ conflicts == 6`).

**The preprocessing caveat is moot** — the bug fully explains the
divergence at parameter parity; no front-end shape difference is
needed. The front-end-preprocessing question remains genuinely open
only as its own line (Verus feeds nla-preprocessed atoms; nla-14/16
territory).

