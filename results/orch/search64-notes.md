# 64-gate counterexample search

No witness found. This is heuristic evidence, not a lower-bound proof.

The evaluator uses bitsets for all 52 positive edge assignments, all 704 maximal independent-set assignments, and the two singleton bases. The negative set was independently audited to dominate all 8192 canonical negative assignments obtained by choosing a point subset and every line avoiding it. Thus a monotone circuit passing these tests computes the exact incidence function. Formal derivatives are propagated gate by gate at both singleton bases. Any exact witness is additionally tested with an independent scalar evaluator on all 8192 canonical negatives.

The initial 65-gate seed comes from `tight-circuit.json`: distributivity changes the last nonincident column star into a final AND of two OR factors. First search exhausts one-gate deletion/replacement and one-gate mutations, then tries a second mutation on near 64-gate candidates. Its ten-minute bound completed 143 of 308 repair sweeps and tested 33,127,686 candidates. No witness.

The unrestricted simulated annealing search made 24,066,384 mutations from 282 near seeds over ten minutes. It found no witness; many walks drifted toward the all-false function, so this is a weak negative result.

Best 64-gate candidate has zero derivatives and no false positives, but misses edge (point 1, line 0). It deletes the first OR gate from the seed.

The 900-second associative-rotation search completed 106 variants and 48,854,455 candidate evaluations without a witness. The two main deterministic-neighborhood runs performed 81,982,141 candidate evaluations in total; these counts include repeated circuits. The annealing count is 24,066,384 iterations, some skipped when no proper mutation resulted. Full completed logs and machine-readable results are stored beside this note.

## Neutral CGP search

`search64_cgp.py` inserts three unused gates before each seed gate, then performs neutral mutations while preserving all 52 positive edge tests, all 704 maximal-negative tests, both singleton values and both formal derivative zeros. It permits active circuit sizes up to 69 to allow neutral structural drift. Complete output is in `search64-cgp.log`. The 600-second run finished without a circuit below 65 gates: 12996427 proposals, 2882599 accepted neutral mutations, 599 active-size changes. This is a heuristic negative result only.

## Completed remaining near-candidate repairs

`search64_continue.py` regenerated the same308 near candidates, skipped the143 already completely checked, and finished all165 remaining full one-gate repair sweeps (indices143 through307). It completed in327.318seconds with38,047,362 evaluations and no64-gate witness. Full output is retained in `search64-continuation.log`; exact hashes and scope are in `search64-continuation-summary.json`. The original and continuation together exhaust this particular308-candidate neighborhood, not all64-gate circuits.
