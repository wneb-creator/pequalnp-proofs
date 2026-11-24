# Alternative6 augmented-pair fitness search

This reviewed variant retains all 24 positive and 64 maximal-negative tests and adds 19 singleton and 147 nonedge-pair negative assignments. Its complete search basis has 254 tests, including230 negative tests, and the balanced negative weight is24/230. The original64 raw negative assignments remain unchanged, so every saved computational witness is independently scalar-replayed on the original88 complete extremal cases. Zero search errors still imply the same target function; the extra tests change the heuristic score only.

The stochastic source copies the independently reviewed Alternative6BalancedMulti source, changing only the problem import, model label, and the negative-error log label. The initializers include valid29/30/32/35 and redundant larger circuits, plus explicitly INVALID one/two/three-cluster biclique compressions. The target remains28. No witness or lower-bound result is claimed.

Author calibration checked96 baselines (83 valid,13 INVALID),384 physical expansions,97,536 augmented scalar cases and8,448 raw scalar cases. Independent review checked48 baselines and144 physical expansions on36,576 augmented scalar cases. Complete logs are included.

Run from this directory with `python3 SearchStochasticAlternative6Pairs.py --seed 14772948 --seconds 1200 --output-dir /tmp/oec/pequalnp-pilot-29/stochastic-alternative6-run-010`, redirecting complete stdout and stderr to a separate log. The actual run is managed by the status-audit agent in its existing local CPU slot.
