Generated 2026-11-25T01:04:58.066602+00:00

# L-meta-2585 counterexample search manifest

Status: no full-function counterexample found. All results below are ordinary Python/CaDiCaL computations, not Lean-checked theorems. Timeouts and interrupted searches establish no lower bound.

Working directory: `/tmp/oec/pequalnp-pilot-46/gap-2585/counterexample/`.
Solver: `/tmp/oec/pequalnp-pilot-46/toolchain/lean-4.36.0-linux/bin/cadical`.
Every solver invocation retains complete stdout/stderr in its `.log`; CNFs are retained. Current generators cap each child process at1900MiB or1500MiB and at300s or less. No network calls are made by these scripts.

## Reproducible completed checks

- `python3 cover_audit.py`: all512 relations on3+3 inputs and all13,009 valid covers. Canonical star circuits satisfy AO2, compute the full truth table, fit the cover cost, and have squarefree edge proof trees.
- `python3 cover_audit44.py`: all18,521 C4-free4+4 relations, one minimum cover each, full256-input truth table and squarefree edge proof trees. Both cover-construction audits passed.
- `python3 census33.py`:16 representative nonempty C4-free bipartite graphs with at most3 vertices per part. No circuit below `m+tau-1`; all SAT instances UNSAT, with the zero-gate one-edge case checked directly. The generator includes all truth-table rows and safe liveness/padding.
- Frozen `c6-macro-and2.cnf` and `c6-macro-or4.cnf`: UNSAT in0.006s and0.217s. These exclude≤2AND with arbitrarily many OR gates, and≤4OR with arbitrarily many AND gates, respectively.
- Frozen `theta-macro-and3.cnf`: UNSAT in0.034s, excluding≤3AND with unlimited OR gates for the9-edge theta graph in `maximum44.json`.
- Frozen `cycle12-macro-topo-and5.cnf`: UNSAT in45.089s, excluding≤5AND/freeOR for the12-cycle graph. It has29 maximal independent sets, so this result exceeds the elementary logarithmic maxterm bound.
- `variable-4x4-and3-46/iteration-003.cnf`: UNSAT after3 rejected graph/circuit models and9 negative cuts,0.38s total. This excludes≤3AND/freeOR for every C4-free4x4 incidence relation containing the diagonal perfect matching. The later degree-ordering/enriched-cut implementation was rerun from scratch under seed47 and also reachedUNSAT.

To replay a frozen CNF, invoke the solver with `-t 300` and that explicit filename, redirecting both stdout and stderr to a new replay log. CaDiCaL exit20 meansUNSAT;10 meansSAT;0 is a timeout/unknown result in these runs.

## Unresolved or interrupted attempts

- `theta-size11.cnf`: full AO2 synthesis one below canonical12 timed out300s.
- `theta-macro-or7.cnf`: old macro search stopped around140s to prioritize another strategy; no verdict.
- `theta-macro-private-or7.cnf`: improved unrestricted-AND/≤7OR search timed out300.062s; no verdict.
- `fano-macro-private-and6.cnf`: stopped around120s without a verdict after Structural identified an existing Lean7AND lower bound, L_meta_634. This run contributes no new result.
-6x6 graph-varying search: `variable6-run.log`, `variable6-continuation-run.log`, and `variable-6x6-and5-46/`. First pass rejected20 candidate graph/circuit representations on full4096-assignment truth tables, then hit a60s query timeout at iteration20,113.29s total. Sorted-degree/enriched-cut continuation at iteration21 used344 constrained inputs and timed out299.14s without a verdict. No full-function witness has been found.

## Soundness scope of the search encodings

`macro_count_search.py` flattens every uncounted-operation cone into a nonempty aggregate of original inputs and earlier counted outputs, retains each counted binary gate, and gives the final output another aggregate. This represents every AO2 circuit with at most the given counted-gate budget, regardless of the uncounted-gate cost. Identical operands are allowed. Prune unused counted gates, then pad at the output with counted copies to obtain exact budget and liveness.

The optional symmetries commute each gate's operand aggregates and order gate maximum predecessors nondecreasingly. The latter is obtained by choosing an available gate of smallest maximum predecessor; newly unlocked gates have a larger predecessor index. Private-boundary constraints allow either both operand-private boundary witnesses or identical-aggregate copies, so minimum-count witnesses and exact-count padding remain represented. Structural independently reviewed the collapse argument; Certificate provided Lean versions of the OR-positive and AND-negative private-boundary deletion facts.

For a fixed monotone graph function, minimal true inputs are its edge pairs and maximal false inputs are maximal independent sets. Agreement on those rows implies full truth-table agreement. Every SAT witness is nevertheless expanded to binary gates and checked on every Boolean input.

`variable_graph_search.py` instead makes the incidence relation part of the SAT model, forces the diagonal perfect matching and forbids every4-cycle. It initially checks all inputs with≤2 true variables. Each model is evaluated on all4096 inputs for6x6; higher-order false positives produce new dynamic truth constraints. All rejected models are retained with their exact `false_positive_count`; zero-error models would be expanded and prominently marked. Sorting left degrees relabels both ends of each matching edge together and preserves all full-function witnesses. Saved assignments permit continuation; previous maximal independent sets enrich later runs. UNSAT of a learned finite instance excludes the specified finite graph/circuit class, but remains an external SAT result, not a Lean certificate.

## Additional files

`genetic_search.py` provides exact graph data, canonical star seeds, pruning and fulltruth validation. It was handed to Toolchain, who owns the faster C++ genetic search in a separate directory; no Python genetic burst was run here.

The exact bound `m+tau-1` for unrestricted circuits on arbitrary C4-free bipartite graphs remains unproved in this work. Literature searches found general non-bipartite single-level separations and differently scoped graph-representation/multioutput results, not a theorem settling this statement.


## Final-round updates

- `variable-fooling-4x4-and3-46/iteration-001.cnf` is UNSAT. This relaxed auxiliary family retains diagonal edges and forbids only opposite-cross pairs, allowing other4cycles. One3AND representation had5 higher-order false positives; CEGAR then reachedUNSAT in0.31s. This is evidence about the proposed broader biclique-cover route, not a new proof of the main gap.
- `audit_rejected_models.py` independently evaluates retained models using scalar Boolean evaluation on every input, checks graph conditions and legal macro parents, and records concrete failure assignments in `model-rejection-audit.json`. All25 models currently fail full semantics; none is a witness. The search generator itself uses whole-truth-table integer bitsets, so this audit uses a different evaluation implementation.
- `cycle8-macro-private-or6.cnf` is UNSAT in76.503s: C8 requires≥7OR even with unboundedAND. This final queued query completed; no solver remains active.

Updated 2026-11-25T01:08:04.893247+00:00


## Frozen archive and successor instructions

Scripts now place artifacts beside their own source file, so the directory can be relocated. The public CaDiCaL executable path remains explicitly configured in the search scripts and may need updating on another machine.

Exact generator profiles were checked byte-for-byte against five completed frozen CNFs in `replay-generator-validation.log`. Replay commands (run on a disposable copy to preserve original logs):

```
python3 macro_count_search.py c6 and 300 base
python3 macro_count_search.py c6 or 300 base
python3 macro_count_search.py theta and 300 base
python3 macro_count_search.py cycle12 and 300 topo
python3 macro_count_search.py cycle8 or 300 private
```

Continue the unresolved6x6 graph search from its retained cuts/models/logs using:

```
python3 variable_graph_search.py 6 300 46 300
```

The continuation discovers its next iteration from retained logs, so omitted large CNFs do not reset model numbering. Its current344-input cutset is `variable-6x6-and5-46/assignments.json`.

Run `python3 audit_rejected_models.py` to reproduce the independent scalar rejection audit. The archive includes scripts, complete stdout/stderr, summary data, rejected models, concrete rejection examples, cutsets, and small completed-UNSAT CNFs. Large/regenerable synthesis CNFs are omitted but listed with sizes and hashes in `ARTIFACT_INVENTORY.json`.

No full-function counterexample, Lean proof, or Lean refutation of L-meta-2585 was produced by this search agent. The finite SAT conclusions are evidence only.

Frozen 2026-11-25T01:11:09.330904+00:00
