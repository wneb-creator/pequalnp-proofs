# Exact-hypothesis K4-incidence CGP search for L-meta-4970

`circuit_cgp.cpp` adapts the earlier CGP program to the fixed bipartite graph with four point inputs and six line inputs, one line for each pair of points. It has 12 edges and minimum vertex-cover size four, so a circuit with at most 14 gates satisfying the posted assumptions would refute the bound. The canonical circuit has 15 gates.

Every evaluated genome uses complete 1024-row truth tables. A semantic star witness is an OR gate computing exactly the OR of a neighbor subset of size at least two. Raw OR reach follows OR parents and stops at every AND gate. Duplicate parents and gates after the designated output are allowed.

The genome has spare gates. To emit a circuit, the program retains the output ancestors plus enough complete witness cones to serve every edge. It never prunes merely to the output cone. Mixed OR gates are forbidden in this retained circuit. A greedy witness selection supplies a valid retained-size upper bound; it is not an exact minimum and does not support a lower-bound claim. Inactive spare genes may be dropped. Printed circuits are checked again after renumbering.

`verify_cgp.py` separately evaluates every printed gate on all assignments, recomputes syntactic two-colour reach, discovers all semantic pure-star witnesses, checks the printed witness set covers all edges, and enumerates vertex covers. It retains unused printed gates.

Positive controls are the canonical 15-gate circuit, a 23-gate DNF with eight required unused witness ORs appended after the output (31 gates), and a 31-gate circuit with six duplicate AND shields and a semantically mixed but syntactically monochrome guard. Negative internal controls reject missing witnesses, an incorrect output, and an active unshielded mixed OR. All controls passed. A two-second smoke run made 2,611,616 mutations and found no circuit below 15 gates. This is heuristic search evidence only.

Build: `g++ -O3 -std=c++20 circuit_cgp.cpp -o gap4970_cgp`.
Usage: `gap4970_cgp seconds seed capacity control-only`.
Verification: `python3 verify_cgp.py output.stdout`.

No long search was launched before independent source review and a fresh root lease renewal.
