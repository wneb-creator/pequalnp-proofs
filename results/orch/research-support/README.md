These are finished supporting inputs and complete logs referenced by the research notes. They are computational evidence, not Lean proofs.

The original search scripts retain their job-specific input paths. `tight-circuit.json` is the 65-gate search seed; `structural-max-independent.json` is the complete 704-row negative test set. Both are preserved here so those inputs survive the container. The signed-code witness/log files support signed-code-analysis.md, and the small-double logs support reduction-design.md and counterexample.md.

`python3 results/orch/research-support/verify-research-data.py` independently checks the two finite signed codes, all 704 maximal false rows, all 704 point-code separation witnesses, all 8192 point-subset information bounds, and the final no-private-block numerical contradiction. Its complete output and empty stderr are preserved beside it. This does not formalize the no-private geometric argument or prove the global lower bound.
