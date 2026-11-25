# Finite checks for L-meta-1770

These are computational checks, not Lean-checked theorems.

## Circuit cases

Canonical functional-state synthesis finds the least AO gate counts for all forests on four and five labelled vertices. Exhaustive ordered circuit enumeration (commutative inputs ordered, repeated functions excluded) checks every circuit attaining those counts. A least circuit cannot repeat an available function because that gate can be deleted and its readers redirected.

- Four vertices: 37 nonempty forests, 180 minimum circuits, 108 in TopForm, no junk gates.
- Five vertices: 290 nonempty forests, 3790 minimum circuits, 2110 in TopForm, no junk gates.
- C5: CaDiCaL says six gates UNSAT, seven gates SAT; the witness was independently evaluated on all 32 inputs. Seven gates plus TopForm plus any junk is UNSAT.
- C6: CaDiCaL says seven gates UNSAT; a standard eight-gate star circuit was independently evaluated on all 64 inputs. Eight gates plus TopForm plus any junk is UNSAT.

SAT encodes exact AND/OR fan-in two, earlier wires, one operation per gate, complete truth tables, used gates, recursive gate ancestry, and semantic dirtiness. TopForm forbids every clean AND ancestor of any AND gate. These SAT UNSAT outcomes have not been converted to Lean certificates.

## Proposed core reduction

A separate exhaustive generator considers each possible graph edge once, taking both absence and presence branches. A presence branch is rejected exactly if it makes a triangle or a four-cycle. At every resulting graph, repeated removal of vertices of degree below three computes the 3-core.

| Vertices | Labelled graphs of girth at least five | Nonempty 3-cores |
|---|---:|---:|
| 5 | 303 | 0 |
| 6 | 3424 | 0 |
| 7 | 53365 | 0 |
| 8 | 1121412 | 0 |
| 9 | 31197241 | 0 |

The proposed core child is therefore vacuous on at most nine vertices, independently of the circuit or target-edge predicate. This agrees with the usual Moore bound: a girth-five graph with minimum positive degree at least three has at least ten nonisolated vertices.

Generator SHA-256: `0e9540af031faa52229fe72170e09a3a13a12ee529cfe575467dc939be3ff97c`.

A further synthesis attempt for the seven-vertex theta graph with path lengths two, three, three, using eleven gates and requiring TopForm plus a junk gate, reached the solver time limit of 180 seconds. It yielded no SAT or UNSAT conclusion. Complete output is archived.
