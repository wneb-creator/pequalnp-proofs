Critical output witnesses for minimum AO2 circuits

Flag: --critical-output-witnesses, at-most only, off by default.
Backup: core_sat_before_critical_output.py. Diff: core-sat-critical-output.diff.
Current sourceSHA9fe3d2a08d970f97fd9cab1ca3a38c0be5e976dab76dcabdc3c36486490b7d7c.

Mathematical scope

If an exact circuit of size<=s exists, choose a globally minimum one. Bypassing either input port of any AND gate yields a circuit of one fewer gate whose output is pointwise greater than or equal to the target. It cannot remain exact, so it accepts a false input. Extend to a maximal false target input: the bypassed circuit stays true, the target stays false, and therefore the changed gate still differs from its kept port. The original operands are10 or01, depending on which port is kept. OR bypass is dual: its output is pointwise smaller, must reject a true input, and that witness can be shrunk to a minimal true target row. Thus every active gate, both orientations, has an operation-appropriate boundary row at which the FULL output changes when the gate is bypassed. This is a completeness restriction for a chosen minimum circuit, not an assertion about arbitrary exact circuits.

Encoding

For each gate j and direction ab/ba, critical_row(j,d,r) selects exactly one boundary row if active(j), and none if inactive(j). Pairwise at-most-one clauses and active-gated at-least-one implement this. Each choice implies the existing iff port witness variable, and requires label(r)=op(j), where AND=0 and OR=1.

One counterfactual vector per j/d stores every input/gate wire value. For wires strictly before j, selected-row clauses equate values with original symbolic row evaluations (input bits are literal). At wire n+j, the new value is NOT op(j), exactly the kept true port for AND or kept false port for OR under the selected10/01 pattern. Every later gate uses the SAME original symbolic op and fanin selector variables to evaluate the counterfactual wires. It may reuse any changed predecessor, so arbitrary fanout and reconvergence are handled.

For each possible original global output index k>=j, active(j) AND output(k) implies the counterfactual output equals NOT op(j), flipping the selected target label. active(j) already implies the selected output is at or after j. Inactive copies have no selected row or output requirement; their acyclic suffix always has a consistent assignment, and do not constrain the underlying circuit.

Validation

Complete script audit_critical_output.py and log critical-output-audit.log; summary critical-output-audit.json.
- Default exact and previous ordered+op-domain CNF, JSON, printed metadata all byte-identical with the flag off.
- Canonical24-in25 and stripped21-in22 controls SAT with all existing flags plus new witnesses. Fulltruth decoder checks65536/8192 inputs.
- Independent model audit checks every409778/258142 clause; all selector patterns; selected-row domains; every muxed prefix and counterfactual suffix bit; actual bypassed circuit output at48/42 independently reconstructed chosen witnesses.
- Extra inactive gate forced duplicate fanins. No row is chosen for either inactive copy; exemption verified.
- New flag alone with at-most canonical pin is SAT. Exact mode rejected.
- All34790 sorted-fanin AO2 DAGs with1..3 gates on2,3,4inputs enumerated. For all224 globally minimum circuits, each gate and both kept ports has an operation-appropriate boundary row where the actual bypassed FULL output differs. This audit recomputes whole truth tables and is independent of SAT clauses.

Ready target q3core23-critical-output.cnf/.json: original16input20edge core,23gatebudget,12729variables356220clauses. Includes all previous ordered at-most flags and both new witness flags. No target solver launched by this task.
