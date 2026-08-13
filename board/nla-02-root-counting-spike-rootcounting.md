- **nla-02** `done` **Root-counting spike (S2-lite).** `RootCounting/Spike.lean`,
  all proven, no sorries: generic sign-invariance-from-rootlessness (IVT
  contrapositive — the checker's cell-sign workhorse), unique-root isolation for
  a concrete polynomial (IVT + `strictMonoOn_of_deriv_pos`), and the Rolle-chain
  bound composing (`Polynomial.card_roots_le_derivative` exists in mathlib!).
  Verdict so far: per-instance counting looks viable without general Sturm;
  final call after higher-degree census specimens (keep nla-10 conditional).
