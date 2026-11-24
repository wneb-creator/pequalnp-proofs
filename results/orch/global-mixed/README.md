# Mixed OR/AND stochastic search

The exact global problem data is unchanged from the independently reviewed global-search snapshot:105 edge-positive tests and25,237 maximal-negative tests, generated from all2^21 left subsets. Every accepted witness is independently scalar-checked on all25,342 tests. The Lean DNF/table certificates can verify a resulting circuit separately.

This model begins with21 point-centered or line-centered stars. It adds1/2/4/8 latent AND helpers,1/2/4 primary-only OR helpers, and1/2/4/8 mixed OR helpers interleaved before hidden ANDs and among star nodes. Mixed OR helpers can read previous AND outputs and feed later AND operands. Some initial mixed OR nodes group existing output stars while preserving the125-gate total. Other helpers begin unused; only the active output cone contributes to cost. Each AND operand is still an unshared OR of selected earlier sources, so this remains a restricted heuristic architecture.

SearchReduce.py expands a source-set circuit, merges any wire signature equal to an earlier wire on the full test basis, and removes disconnected gates. It checks the rewired output signature again. The record hook tries this deterministic reduction for valid circuits of structural cost<=127, saves any<=124 result after scalar verification, and records up to32 distinct dirty-AND signatures among valid125-gate circuits. Neither the reducer nor the recording hook changes mutation or objective evaluation. No smaller circuit has yet been found.

Validation:1000 random30-gate circuits checked on all64 assignments; a padded global126-gate circuit reduced to125 and scalar-checked on25,342 tests. Eight mixed-model baselines were scalar-checked on the full basis, and4000 baseline/mutant expansions checked topology, active-cone cost, exact signatures and reduction. The independent reviewer checked another300 random circuits and240 mixed expansions; complete logs are included.

Command, from repository root:
```
python3 results/orch/global-mixed/SearchStochasticPlaneMixed.py --seed 14772909 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-plane-003
```

Separate completed diagnostics included for preservation: alternative6 general binary size28 hit its1200-second cap with no verdict. C6 size8 with an explicit dirty AND, complete12-element graph symmetry and minimality pruning was UNSAT in2.48s. The latter is a computational restricted/exact-size result, not a Lean proof. Symmetry-reduced alternative6 size28 is currently running separately.
