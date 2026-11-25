# L-meta-1031 final finite-search checkpoint

All included runs have finished. These are external computations, not Lean certificates or a proof/refutation of L-meta-1031. No below-canonical graph circuit was found. All current source programs and graph inputs are included; earlier snapshots retain unchanged logs omitted here. No solver binary or generated CNF is included.

## Exact-size and restricted-model caveats

The total-size synthesis models enforce distinct nonconstant wire functions, distinct binary fanins, and live gates. They search exact size k. UNSAT at k alone does not exclude every smaller size unless a separate lower bound is available. Prior matching3 size11 UNSAT must be read with this caveat. Count-only models allow unused charged-gate padding, so their reviewed UNSAT results are at-most bounds. Minimum-AND pruning additionally requires that smaller counts have been excluded.

The new `counter_multi_count.py` supports several target outputs with the existing naive free-cone budget. `counter_multi_shared_budget.py` strengthens that budget by charging each distinct free-cone source subset once. Selector words are padded to common global source indices, so an identical conjunction can be computed at its first occurrence and reused. All cones are nonempty, preventing cardinality-minus-one underflow, and bit width prevents modular undercount. Independent source review passed. Proper-subconjunction sharing is still omitted; hence UNSAT excludes only this restricted construction. SAT cost claims require the full truth-table check to pass. Optional `--fixed` merely fixes all source selectors for a positive control and is not enabled in target searches.

## Completed results

* Fano incidence, minimum6AND with reviewed dominance pruning: UNKNOWN180seconds. The unrestricted at-most5AND result is UNSAT in the prior snapshot.
* Generalized Petersen G(7,2),14 vertices,21 edges,cover9,girth5,49 maximal independent sets: at most8AND with freeOR is UNKNOWN180seconds. Inventory found no accepted bound for this graph.
* Matching3 plus four parity triple-OR outputs: cone-model10OR+3AND positive control is SAT9.21seconds with full64-row correctness;9OR+3AND is UNSAT58.44seconds in the restricted model.
* The single-center C8 attachment was abandoned before solving when inventory found accepted general theta exactness (`L_meta_615`). Input/control data prepared before that discovery are retained.
* C8 plus two auxiliary OR outputs, on pairs{0,3} and{4,7}, uses24 decisive rows: all graph edge pairs and maximal independent sets, four auxiliary singletons and two complements, each classified by graph truth. Attaching two new star centers would produce a10-vertex,12-edge,girth5 graph with cover6 and canonical17. A hypothetical12-gate multioutput circuit would yield16 gates; this implication alone would not refute the posted star-profile existence statement.
* The explicit13-gate binary C8 control is SAT and passes all256 assignments. General multioutput size12 is UNKNOWN240seconds. The unconstrained9OR+4AND shared-cone control search is UNKNOWN30seconds, while fixing the known13-gate control yields SAT and full256-row correctness. Target8OR+4AND is UNKNOWN60seconds; target7OR+5AND is UNSAT16.16seconds in the restricted model.
* C5 size7/3AND with nonempty cone-local star ownership is SAT0.136seconds. A separate binary evaluator confirms the three owned edge sets are nonempty stars.
* Petersen-minus01 size13/5AND (thus8OR), constrained to star ownership, is UNKNOWN60seconds. Any star8OR witness here would refute only the proposed profile-conditioned OR lower bound, not the canonical total bound or the posted statement. Size14 probes additionally use normalizations justified for minimum circuits; they could exclude redundant nonminimum star-profile circuits.

Additional generated graph inputs with no matching run log were not searched. Full solver stdout/stderr and all discovered control witnesses are preserved.

The final Petersen-minus01 size14/6AND star-profile probe finished: UNKNOWN at 60.13538718223572 seconds. Its complete logs are included.
