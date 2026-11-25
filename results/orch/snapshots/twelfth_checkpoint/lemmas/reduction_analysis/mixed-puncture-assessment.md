# Mixed point/line punctured core assessment

The four-cap puncture is a sound, smaller search parametrization worth one bounded lane. It is a subclass of the previous four-owner 18-paid-gate model, not a broader circuit class. No 15-gate exact core has been found here.

## Exact sufficient model

Retain point owners 0,1,2,6, and move their two incidences on line13 to the outside. The remaining core has14 edges on13 raw inputs:

`[0,1,2,6,14,15,16,20,21,22,23,24,25]`.

Nine outside point stars cost44 gates including their eight combining ORs. The partial line13 star costs2 gates, and combining it with the point stars costs1, giving an exact47-gate outside circuit. A15-gate core and final combining OR would total63.

The available37 logical inputs are13 raw inputs and24 optional/fixed OR features. There are five outside triples, each permitting at most one of its three pair prefixes; three fixed line pairs; and the fixed point pair0 OR1. Only one USED optional pair in each group is compatible with the47-gate outside cost. The triple outputs themselves are fixed features.

The executable assembler validates all gates/references/output, removes unused core gates, chooses compatible outside prefixes from actual cone usage, and produces a26-input circuit. Independent exact-DNF checks cover all243 prefix choices, every feature wire,15 direct optional-feature outputs, and five invalid-input fixtures. The raw17-gate star calibration restores exactly the52 target edges at65 gates. This calibration is overbudget and has four core ANDs, so target-only lower-bound/dirty cuts must be disabled for it.

## Necessary search restrictions

All13 raw coordinates have explicit pivotal witnesses while every feature value stays fixed. Thus any exact output cone must directly read all13 raw inputs. A binary cone of at most15 paid gates can use at most three distinct feature inputs. If all three are used, its15 gates form a read-once tree on those16 distinct terminals; there is no capacity for repeated direct reads or reconvergence. At two features there is only one such excess incidence available.

The core has16 maximal negative assignments, with pairwise-positive joins. At most four ANDs forces saturation of the selector bound, hence all core ANDs are sound on independent inputs. Pure OR features preserve joins and monotonicity. Since all outside star ANDs are also sound, a completed63-gate circuit would contradict the checked pair-clean64 bound. Therefore an exact15-gate core needs at least five ANDs. This transfer is a mathematical justification using checked generic ingredients and finite data, not a new Lean theorem in these files.

At exactly five core ANDs the assembled full circuit has15 ANDs and48 ORs. The parametrization therefore targets a different count profile from the original13-AND point-star baseline.

## Relation to earlier models

Moving the partial-line term back into the core uses a point OR, an AND with line13, and a combining OR. Hence a successful15-gate punctured core becomes an18-gate full four-owner core in the old model. The benefit is a smaller search space with an exposed point-side OR and a strong direct-read budget; the class of represented full circuits is not enlarged.

The three-collinear puncture has12 pivotal raw inputs but a9-gate budget, contradicting the binary direct-support lower bound11. It is retired. A four-collinear puncture similarly has16 raw inputs versus13 paid gates, so the same argument excludes it. A three-collinear-plus-one-owner puncture plausibly has14 pivotal inputs and14 paid gates, leaving at most one feature; it was not selected for the final lane.

## Optional necessary kernel

Zeroing the four private raw lines5,9,10,11 (full15,22,23,24) leaves a9-raw-input,10-edge theta graph: the once-subdivided K4 with one edge removed. The only nontrivial surviving features are line14 OR line21, line16 OR line25, and point0 OR point1. There are11 maximal negatives and every remaining raw coordinate is pivotal with these features fixed.

The data also gives an explicit pivotal witness at each of four successive private-variable eliminations, after singleton/empty feature aliases are normalized. The existing encoded gate-elimination method should yield a necessary11-paid-gate kernel. That new four-gate-saving implication has not been formalized here. A kernel witness would not automatically restore the sufficient15-gate original core. No solver was launched for this kernel.

## Files

- `status_review/punctured-four-arc.json`: independently generated source packet.
- `punctured_mixed_assembler.py`: executable cost-compatible assembler, independently approved SHA256 `10b0c477180d55dcae2b4eeab307be8b8c47829d3ec8d6ef64da8c262ae3923d`.
- `punctured-four-arc-calibration65.json`: exact65-gate calibration.
- `punctured-four-arc-audit.json` and assembler log: complete finite-check results.
- `punctured_kernel_restriction.py`, `.log`, and `punctured-four-kernel.json`: zero-private restriction and sequential pivotal data, explicitly scoped as computational evidence.
