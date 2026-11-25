# L-meta-1772 second search batch

These artifacts are computational evidence, not Lean lower-bound proofs and not a refutation of L-meta-1772.

The solver and base encoding are described in `../search/README.md`. This batch freezes `circuit-sat.py` at SHA256 `46768beb0bc769aa732dcc7f66c8da4cabfd88f1076447aaa5f033d6b3cc6b42`. Set `PNP_CADICAL` to an installed CaDiCaL executable and `PNP_SEARCH_DIR` to the output directory before replaying commands.

## Additional results

| Test | Result |
| --- | --- |
| All 37 nonempty labelled four-vertex forests at their BFS minimum sizes, forcing an unowned AND | All UNSAT in the normalized model |
| C6, 8 gates, forcing an unowned AND | UNSAT in 10.6 seconds |
| C7, 10 gates, forcing an unowned AND | UNKNOWN after 120 seconds; with canonical-first symmetry UNKNOWN after 180 seconds |
| Subdivided K4 stress graph, 12 gates | UNKNOWN after 300 seconds |
| Same stress graph, 13 gates, forcing an unowned AND | UNKNOWN after 300 seconds |
| Same stress graph, 13 gates, every AND required to own an edge | UNKNOWN after 60 seconds; an explicit 13-gate ownership witness was separately checked in Lean |
| Same stress graph, 12 gates, optional minimum-circuit pruning | UNKNOWN after 180 seconds |
| All 34 unlabeled graphs on five vertices, without girth restrictions | All 33 nonempty cases produced an all-owned SAT model; the empty graph was handled directly; K5's lower bound remains unresolved |

The five-vertex census was performed by the algebraic-route agent; its generator, complete results, progress log, and validation metadata are the four `general5*` files. The empty graph uses the trivial zero-gate circuit and did not invoke SAT. For 32 nonempty cases, all tested smaller sizes were UNSAT; sizes below the number of essential vertices minus one were excluded by the informal binary fan-in dependency bound rather than solver calls. K5 has a size-10 ownership witness and a smaller-size timeout. These findings support existence of an ownership witness in the finite cases, but do not establish that every minimum circuit owns every AND.

The four-vertex forest census used the explicit graph list and minimum sizes in `../search/small-circuits-n4.json`. Each nonempty graph was passed to the encoder with its recorded minimum size, `--unowned-and`, and `--seconds 5`. Full individual solver logs and the combined results/progress logs are included.

## Stress graph and checked upper bound

`subdivided-k4.json` describes vertices 0 through 7 and edges
`03, 12, 04, 24, 15, 35, 06, 16, 27, 37`.

The separate Lean file `../lemmas/StressGraph.lean` checks that this graph has no triangle and no four-cycle. It also checks a 13-gate monotone circuit that computes exactly the graph function and whose every AND owns an edge. The construction uses stars centered at 0,1,2,3 with neighbor groups `{3,4,6}`, `{2,5,6}`, `{4,7}`, `{5,7}`. No minimality assertion is made.

Replay examples:

```sh
python3 circuit-sat.py --graph cycle6 --gates 8 --unowned-and --seconds 60
python3 circuit-sat.py --graph cycle7 --name cycle7canonical --gates 10 --canonical-first --unowned-and --seconds 180
python3 circuit-sat.py --graph file:subdivided-k4.json --name subdividedk4 --gates 12 --seconds 300
python3 circuit-sat.py --graph file:subdivided-k4.json --name subdividedk4 --gates 13 --unowned-and --seconds 300
python3 circuit-sat.py --graph file:subdivided-k4.json --name subdividedk4 --gates 13 --all-owned --seconds 60
python3 circuit-sat.py --graph file:subdivided-k4.json --name subdividedk4pruned --gates 12 --minimal-pruning --seconds 180
```

## Optional minimum-circuit pruning

The `--minimal-pruning` experiment additionally requires each gate to be true on some edge, each OR gate's operand vectors to be incomparable on edge inputs, and each AND gate's operand vectors to be incomparable on maximal independent inputs. A bypass argument suggests these are necessary for a minimum circuit. That argument has **not** been checked in Lean here, and this option must not be treated as a proved complete model. It was used only for the explicitly named `subdividedk4pruned` experiment, which timed out.

All ordinary normalized-model caveats from the first batch still apply. Solver exit 0 at a limit is UNKNOWN. Full solver stdout and stderr are preserved for the forest census and the larger named cases. The general five-vertex census includes summaries and a progress log, but its individual full solver logs are not archived here. Exact CNFs and encoding metadata are included for the larger named cases.
