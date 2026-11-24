# Broader Triangle9 search with explicit invalid near misses

This extends the reviewed Triangle9 source with up to twelve latent AND helpers and eight prefix OR helpers. Extra AND helpers beyond the nine point centers are dormant in the initial valid circuit. Mutation, objective, and exact active-cone gate costing are unchanged. Matching warm starts remain valid at59 gates; the baseline is53 and the target52.

The recorder preserves at most12 distinct near misses for each1–4 search-error count at size≤52, plus24 cases with at leasttwo active dirty ANDs and at mostsix search errors, sampled every256steps. All are explicitly INVALID. Each is physically replayed on404 complete extremal tests, and the concrete mistaken assignments are independently scalar-checked on all557raw extremal inputs. A recorded near miss is a repair seed, never a witness. Valid candidate handling retains the prior full557 scalar verification and Lean-verification requirement.

Author calibration:864 expanded baseline/mutant checks and288 valid baselines on all557raw tests. Independent review:96 full-grid valid baselines,288 physical checks, source review PASS. Reproduce a run with `python3 SearchStochasticTriangle9Near.py --seed 14772919 --seconds 1200 --output-dir <scratch-directory>`.
