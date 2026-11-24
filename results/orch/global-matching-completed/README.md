# Completed global matching warm-start search

This preserves the full stdout and stderr log from the 1,200-second global search using the independently reviewed source in `../global-matching/`. It completed 8,093,696 mutations with 63 matching warm starts and retained the known 125-gate circuit. The matching fixtures start at 131 gates; no circuit of size 124 was found. This heuristic run does not establish a lower bound.

Reproduction uses `SearchStochasticPlaneMatching.py --seed 14772913 --seconds 1200 --output-dir <scratch-directory>` from the sibling frozen package. The complete output is preserved in `stochastic-plane-run-004.log`; its first record confirms the seed and model metadata.
