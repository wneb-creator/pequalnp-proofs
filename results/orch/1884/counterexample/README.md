# L-meta-1884 targeted synthesis

These are external computational experiments, not Lean proofs of the posted lower bound.

The generic model searches eighteen binary AND/OR or unary NOT gates on the ten original
Petersen inputs and the free input `!x0`. Gates read earlier wires, and the last gate is the
output. Every one of the 1,024 input assignments is constrained. CaDiCaL reached its
600-second wall limit with no SAT or UNSAT verdict. Peak RSS was 286,716 KiB.

Two fixed twenty-gate positive controls passed. Each decoded circuit was independently
checked on all 1,024 inputs and every generated CNF clause. The twenty-gate upper bound
already exists in `lean/PEqualNP/Outside/L_meta_587.lean`; these controls do not claim a new
mathematical result.

The monotone-internal experiment permits AND/OR gates and the free complemented input.
For either fixed value of `x0`, the circuit is monotone in the other nine inputs. Its 38
cofactor minimal-positive and maximal-negative rows therefore suffice; the generator
checks domination coverage of all 1,024 inputs. The generic CEGAR experiment also starts
with these rows as necessary constraints, allows internal NOT gates, and adds failing
assignments after independently checking each SAT candidate on the full truth table.

Independent review confirmed the encoding, selector and gate clauses, controls and
extremal-row argument. A hypothetical UNSAT result would still require normalization and
a formal encoding bridge before proving the full posted statement, which permits other
unary inputs, arities and invalid wire reads.

Programs retain the job's original absolute scratch paths. Regenerate CNFs with
`petersen_sat.py`; `solver_limit.py` invokes the installed CaDiCaL with a wall limit and
address-space limit. Large deterministic CNF files are omitted from this archive.
Complete solver stdout/stderr and compact metadata are retained. `manifest.json` records
checksums of the archived completed experiments.
