# L-meta-1884 targeted synthesis

These are external computational experiments, not Lean proofs of the posted lower bound.

The generic model searches eighteen binary AND/OR or unary NOT gates on the ten original
Petersen inputs and the free input `!x0`. Gates read earlier wires, and the last gate is the
output. No search produced a fully correct counterexample or an UNSAT result.

| Experiment | Constraints | Outcome | Elapsed seconds | Peak RSS KiB |
| --- | --- | --- | ---: | ---: |
| Generic eighteen gates | All 1,024 input rows | Wall limit, exit 0; no verdict | 600.153 | 286716 |
| AND/OR eighteen gates | Free `!x0`; 38 exact cofactor rows | Wall limit, exit 0; no verdict | 600.015 | 136504 |
| CEGAR first candidate | General gates; 38 necessary rows | SAT, but rejected on 856 of 1,024 rows | 10.867 | 29184 |
| CEGAR refinement | 54 necessary rows | Wall limit, exit 0; no verdict | 120.009 | 71688 |
| Petersen minus vertex zero | Sixteen gates, exactly one NOT, all 512 rows | Wall limit, exit 0; no verdict | 300.028 | 166444 |
| Unique polarity readers | Eighteen AND/OR gates; sole raw zero reader is OR, sole complemented-zero reader is AND | Killed by signal 9 before its 300-second limit; no verdict | 173.795 | 57544 |

Four fixed positive controls passed. The two twenty-gate controls and the twenty-four-gate
unique-reader control were checked on all 1,024 inputs and every generated CNF clause.
The sixteen-gate vertex-deleted control was checked on all 512 inputs and every clause.
The twenty-gate upper bound already exists in `lean/PEqualNP/Outside/L_meta_587.lean`;
these controls do not claim a new mathematical result.

The monotone-internal experiment permits AND/OR gates and the free complemented input.
For either fixed value of `x0`, the circuit is monotone in the other nine inputs. Its 38
cofactor minimal-positive and maximal-negative rows therefore suffice; the generator
checks domination coverage of all 1,024 inputs. The generic CEGAR experiment also starts
with these rows as necessary constraints, allows internal NOT gates, and adds failing
assignments after independently checking each SAT candidate on the full truth table.

Independent review confirmed the core encoding, selector and gate clauses, controls and
extremal-row argument. A hypothetical UNSAT result would still require normalization and
a formal encoding bridge before proving the full posted statement, which permits other
unary inputs, arities and invalid wire reads.

Programs retain the job's original absolute scratch paths. Regenerate CNFs with
`petersen_sat.py`; `solver_limit.py` invokes the installed CaDiCaL with a wall limit and
address-space limit. Large deterministic CNF files are omitted from this archive.
Complete solver stdout/stderr and compact metadata are retained. `manifest.json` records
checksums of the archived completed experiments.
