- **Added:**
  Tactic :tacn:`rewrite_bfs`, a variant of :tacn:`rewrite` that selects the
  occurrence used to instantiate the rewriting lemma by a breadth-first
  (shallowest-first) search that stops at the first match, instead of the
  default depth-first outermost-leftmost order. Besides changing which
  occurrence is picked for pattern left-hand sides, it can be significantly
  faster when a shallow target occurrence sits next to deep, same-head subterms
  that are expensive to reject (such as large implicit arguments), since it
  never descends below the match it commits to
  (`#00000 <https://github.com/rocq-prover/rocq/pull/00000>`_).
