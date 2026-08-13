- **nla-22** `todo` **Dependency work-queues, Z3-identical.** Replace the
  brute-force fixpoint re-run (+54% tactic calls on the stress goal for
  confirmation) with Z3's scheduling: track which facts changed per round
  and re-run a generator for monomial m only when one of m's inputs (factor
  bounds, factor signs, atom bounds) gained a fact. Directive: the goal is
  to be IDENTICAL to Z3's behavior, so port the todo-list structure from
  nla_core/monomial_bounds rather than inventing an equivalent.
