# Immutable stochastic search archive, 2026-11-25 10:58 UTC

No <=27-gate witness has been found. Search failures here are bounded heuristic failures, never UNSAT claims.

- `stochastic-global-cse.log`: completed900-second global CSE trial,471,190,736 mutations, best28.
- `stochastic-branch-biased.log`: completed600-second structural-bias trial,226,395,932 mutations, best28.
- `stochastic-global-diverse.cfg`:640 exact quiet seeds:64 at28 gates,512 mixedp9 at29 gates,64 mixedp8–p12 at31 gates.
- `stochastic-config-verify.py` and `stochastic-global-diverse-verification.json`: independent all16,384-row truth and direct two-derivative verification of every seed, exact21-edge/37-maximal-negative boundary census, distinct earlier operands, and all wires live. PASS.
- `stochastic-mixed-seeds.py` and `stochastic-mixed29-seeds.json`: new512 mixedp9 seeds, allBplus15/Bzero1, with internal and root factorizations and dualities.
- `stochastic-branching-summary.json`: structural diagnosis of earlier seeds and near-candidates; all old exact28 and one-edge-missing27 families lie in the pure7-input eligible class withBzero1.
- `stochastic-frontier-verification.json` and the completed branch-biased frontier/near snapshots: independent full truth-table false-positive/negative counts and direct traces. No27-gate witness.
- `stochastic-diverse.cpp`: frozen source of the next20-minute variable-length seed search; its mutable active outputs are intentionally excluded.

Every copied file has a SHA256 and byte count in `MANIFEST.json`. To reproduce the seed verification from this directory: `python stochastic-config-verify.py stochastic-global-diverse.cfg`.
