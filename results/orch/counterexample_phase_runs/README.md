# Completed compact phase searches

Both searches returned UNKNOWN, with no SAT model and no UNSAT certificate:

- `dual-phase-k8-p1-fullneg`: at most 24 gates, eight abstract AND nodes, one shared positive/negative helper after the first AND, selected-wire budget 33, 571 rows. The run used an exact 27-gate masked-input seed as phase preferences and ended after 300.04 seconds.
- `dual-phase26-k8-p1-fullneg`: at most 26 gates in the same template, budget 35, 571 rows. It used the ABC-transformed 27-gate seed and ended after 119.19 seconds. This was a seed search; a 26-gate circuit would not refute the posted statement.

The complete driver and solver stdout/stderr, exact source snapshots, commands, seeds, row lists, schemas, and phase metadata are retained. Large CNFs and phase vectors can be regenerated from those inputs. These are restricted construction searches; their timeouts establish no lower bound.

A separate finite heuristic checked removal of three non-NOT, non-output gates from each of the two archived 27-gate seeds, replacing each deleted output by either of that gate's two inputs. Among 36,800 rewired circuits, 34,300 retained a NOT in the output cone. The best has 24 gates and 126 truth-table mismatches, so it is not a counterexample. Its exact gates and source/deletion choices are retained as `best24-from-masked27.json`; `best24-masked-ordered.json` is a function-preserving normalized phase seed. This search says nothing about circuits outside that deletion family.
