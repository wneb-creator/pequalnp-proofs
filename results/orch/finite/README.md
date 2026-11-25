# Finite checks for pilot 158, L-meta-4970

These are computational checks, not Lean proofs of the universal statement. UNSAT logs are solver evidence, not Lean certificates. A timed-out search has verdict UNKNOWN.

## Exhaustive circuit enumerators

`counterexample-small.cpp` enumerates backward binary AND/OR circuit prefixes on at most six inputs. Operand order is canonicalized because both operations commute; repeated operands and duplicate or dead gates are retained. OR reach is tracked exactly, and a prefix is rejected when an OR gate reaches both colours. Every earlier wire remains a possible output, so appended dead star witnesses are included.

Graph targets are all nonempty bipartite graphs in the chosen split that have no four-cycle and no edge joining two degree-one vertices. The omitted graphs cannot satisfy the star-witness hypothesis. A target appearing below `|E| + tau - 1` is checked for all required semantic pure-OR witnesses. The saved runs report no target below its bound even before the witness test.

`refined-ledger.cpp` tests auxiliary component inequalities. Mode 0 uses all OR gates computing an exact OR(Q), where Q has at least two elements and lies in one graph neighbourhood. Mode 1 uses OR gates with at least two singleton-true inputs, whose singleton support lies in a unique neighbourhood and whose function is below that neighbourhood OR. Both modes require the posted, exact pure-OR star witnesses separately.

Components merge overlapping supports at the same centre. Write L for the sum of component union-leaf cardinalities, q for the number of components, and Nnon for the number of gates outside the family. The adjusted all-family inequality is:

    Nnon + L + 1 >= q + tau + |E|.

The program enumerates inclusion-minimal serving component subfamilies. Each has a private edge. It checks whether at least one satisfies the adjusted inequality with its selected gate count, and whether at least one satisfies the stronger unadjusted inequality:

    Nnon_selected >= q_selected + tau - 1.

The initial unpruned pure-family five-gate log predates the stronger selected-family check; the expanded-family five-gate log and pruned six-gate logs include it.

Compile using a C++17 compiler, for example `g++ -O3 -std=c++17`. Arguments are:

    counterexample-small n p maximum_gates
    refined-ledger n p maximum_gates family_mode [pruning]

Both programs reject n outside 2..6 and gate counts outside 0..31. Family mode is 0 or 1; pruning defaults to 0. With pruning 1, duplicate semantic-value/OR-reach wires are omitted, and adjacent independent gates are ordered by their operation/value/reach key. The pruned results are separate from the unpruned exhaustive five-gate results. This pruning argument has not been formalized in Lean.

## C6 synthesis

`circuit_sat.py` generates DIMACS for the fixed six-cycle. It encodes all 64 input assignments, one-hot unordered operand pairs, operation bits, and optionally exact OR reach. Gates other than the output must be used. Exact-size padding may use AND(output, output), and duplicate OR gates can be replaced with AND duplicates without increasing the OR count or T.

These SAT cases relax the posted theorem by omitting star witnesses. UNSAT therefore excludes a counterexample within the specified case. The nine-gate/four-OR run timed out and is UNKNOWN. `decode_circuit_sat.py` independently evaluates a satisfying model; the eight-gate positive control computes the target and satisfies every star witness.

    python3 circuit_sat.py gate_count max_OR_count T_zero_flag output_basename
    cadical -t seconds output_basename.cnf
    python3 decode_circuit_sat.py output_basename solver_log

## Refined-ledger synthesis

`refined_ledger_sat.py` directly searches for a violation of the adjusted all-family inequality on C6 plus one pendant edge: seven inputs, seven edges, and vertex-cover number three. It uses all 128 input assignments, permits dead gates, and allows any gate as output.

Every graph degree is at most three, so supports of cardinality at least two at a fixed centre intersect. Thus there is at most one component per centre. Exact family classification, directed-edge coverage, and the strict ledger inequality are encoded as equivalences and a cardinality constraint. The pure-family nine-gate search is UNSAT. The expanded-family nine-gate search timed out and is UNKNOWN.

    python3 refined_ledger_sat.py gate_count family_mode output_basename [enforce_violation]
    python3 decode_refined_ledger_sat.py output_basename solver_log

Setting the optional last argument to 0 omits the violation constraint for a positive control. The decoder independently checks every input assignment and all classification and ledger values. The standard nine-gate control has ledger slack zero.

## Sparse Fano synthesis

`sparse_circuit_sat.py` uses a complete, smaller set of test inputs and factorized one-hot operand selectors. The supplied Fano data contains 21 edges, 37 maximal independent sets, 14 singleton assignments, and 56 star-support complements: 128 distinct rows altogether.

For a monotone circuit, truth on every edge pair and falsity on every maximal independent set imply exact graph-function computation. Likewise, truth on each singleton in Q and falsity on the complement of Q characterize the pure OR(Q).

    python3 sparse_circuit_sat.py graph_json gate_count kind output_basename
    python3 decode_sparse_circuit_sat.py output_basename solver_log

Kinds are `full`, `pure`, `expanded`, and `control`. Full mode enforces `gate_count < |E| + tau - 1`; a validated SAT model would refute the posted bound. Pure and expanded modes seek a refined-ledger violation and require maximum degree three. Control mode omits the violation condition.

The pinned 27-gate Fano control is independently verified on all 16,384 assignments, with T = 0 and all star witnesses. The 26-gate full search timed out at 180 seconds and is UNKNOWN. It proves no lower bound.

The finite_audit subagent independently reviewed the refined and sparse SAT encodings, their decoders, the refined component evaluator, and the supplied Fano data. It found no encoding defect within the documented bounds.

## Normalized residual bounds

`normalized_bounds.py` evaluates known residual circuits D, with every AND gate dirty, T = 0, and the posted pure-star witnesses. It enumerates every wire pair whose conjunction is below the target graph function, then finds the minimum number of such pairs whose union covers every edge. This is exact finite set cover: dominated coverage masks can be removed because all pairs have equal cost. The chosen union is independently checked against the full truth table.

It tests the proposed inequalities `|E| <= A + J + |U|` and `tau <= B + |U|`, where A counts eligible OR gates, B the other OR gates, and J the dirty AND gates. Both exact pure-star and expanded singleton-support/below-neighbourhood definitions of A are evaluated. The six saved examples include an expanded-only star gate; the standard C6 and Fano residuals attain equality in both inequalities.

`normalized-enumeration.cpp` applies the same tests to every residual prefix and every eligible graph in a small split. It does not require any existing wire to compute the target. Its command-line arguments and bounds match `refined-ledger.cpp`. The unpruned 2×2/four-gate run checked 747,439 prefixes and 379,984 qualifying residuals. The unpruned 2×3/four-gate run checked 2,614,162 prefixes and 2,675,301 qualifying residuals. Both inequalities passed using expanded A and the exact minimum |U|.

The Python normalized-model evaluator was independently audited. The additional C++ normalized enumerator was sent to the parent for independent review before archival; its logic mirrors the audited evaluator but is not covered by the earlier audit verdict.

A separate 30-second SAT test pinned the C6-plus-pendant active star centres to {0,3,4,5} with at most four star gates, seeking failure of the stronger selected-subfamily inequality. Its result is UNKNOWN; the extra clauses are saved explicitly.
