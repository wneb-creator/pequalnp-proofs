# Shared local stochastic search with dirty warm-start capture

This is the independently reviewed shared-OR local search plus a recording hook. The hook saves up to64 distinct semantic signatures of active dirty AND gates in valid circuits of size at most35. It recomputes each active node on the full88-case extremal basis and requires the expanded circuit to pass the94-case scalar check before saving. The search RNG, objective, mutations, and validity criterion are unchanged.

A dirty warm start of size35 is not a refutation. It may expose reusable subexpressions or redundant gates for a later improvement. Any size34 witness still requires Lean verification. Run002 uses seed14772902 and a1200-second cap; it was running when this package was frozen. No smaller witness is claimed.

Independent incremental review by counterexample_search: PASS. Source SHA2563e1a2df8538e8a22e5abe08a41106ecaa922ab5cbe1b7f9c65cdb762e72cadcb. Original shared implementation was separately reviewed against400 random genomes, and its baseline generator checked on200 exact warm starts.
