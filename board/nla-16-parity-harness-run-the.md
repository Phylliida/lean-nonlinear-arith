- **nla-16** `todo` Parity harness: run the full workspace nonlinear corpus
  through the tactic; compare against Z3 site-for-site; census-style report.
  Acceptance: no site that Z3 closes and we don't.

  Owned items (accumulated): G8/G9/G10; the R-iii pd-driver/int1
  z3-binary differential probes via `/tmp/z3-4.12.5`; the mk_ineq_atom
  normalization gap; the glue-subsumption watch; the perf watch
  (mkDecideProof whnf on big tables; intervalMagnitude's
  verbatim-quirk formula is the first suspect if pacing drifts);
  **the div/mod × nlsat-tier composition gap (nla-14 Slice-4 review
  R-ii, 2026-08-14)** — a VC needing both div/mod reasoning (L1-owned)
  and nlsat-tier nonlinear lemmas (L2) is unclosable today (loud
  div/mod reify failure, never a wrong close) while z3's solver-6
  closes it in one search; if the corpus shows contact, the fix is
  reifying div/mod subterms as fresh vars + the Euclidean defining
  facts as extra root hyps over the ℝ casts.
