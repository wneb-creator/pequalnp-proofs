# Incidence graph searches and auxiliary score obstruction

This bundle is separate from the frozen results/orch/search bundle. No counterexample to posted L-meta-4970 was found here.

## Exact auxiliary counterexample

`score-counterexample-q5.py` constructs the incidence graph of the projective plane PG(2,5), using normalized nonzero vectors over the prime field, and a 959-gate circuit. The graph has 31 vertices in each colour, 186 edges, and a perfect matching of size 31. Pairwise neighbourhood intersections are checked to have size one, proving the finite C4-free property. The matching and one full colour class establish cover number 31.

The circuit uses adjacent anchor variables x,y. Replacing each literal z by x OR z gives x OR F; analogously for y. Their AND is F because xy is an edge. One idempotent AND buffer per anchor enforces syntactic T=0 for mixed literal sums. The two constructions share x OR y. Ninety-three unused binary OR gates pair the six neighbours at each left vertex, supplying every required star witness.

Every gate is evaluated as an exact minimal monotone DNF antichain, so validation covers every assignment without enumerating 2^62 assignments. The complete output DNF equals the 186 graph edge terms. The program also checks binary AND/OR gates, backward references, T=0, all star witnesses, the selected ancestor cone, and exact singleton supports.

For B counting zero-singleton-output ANDs with two singleton-positive operands, and M counting ORs with two distinct singleton-positive input wires and output singleton support of size at least two, this circuit has B=1 and M=214. Every gate lies in the output-plus-witness ancestor cone. Thus 2B+M=216 < |E|+tau=217. This refutes the proposed auxiliary inequality under the full posted hypotheses. It does NOT refute the posted gate bound: the actual circuit has 959 gates. This verification is Python exact finite computation, not a Lean certificate.

Reproduce with `python3 score-counterexample-q5.py`; its JSON and complete log are included. It uses only Python standard libraries.

## Targeted K4-incidence searches

`or-synth-incidence.py` allows unrestricted free AND gates and budgets the OR gates, requiring the graph function and all posted star witnesses. It uses the same exact monotone extreme-input and star characterization as the earlier bundle; SAT models are independently evaluated on all assignments.

- K4 incidence with at most 10 OR gates: UNKNOWN / timeout at 180.012 seconds.
- K4 minus one edge incidence, at most 8 OR gates: UNKNOWN / timeout at 180.012 seconds.

`or-synth-incidence-gadget.py` additionally supports `matchingprefix`: six fixed pure binary OR witnesses come first, two for a perfect matching of K4 vertex variables and four for the pairs of nonmatching incident edge variables. These already witness all twelve incidence edges. This is an explicitly restricted search.

- Matching-prefix K4 with at most 10 OR gates: UNSAT in 0.226 seconds.
- Matching-prefix K4 with 11 OR gates: SAT in 0.197 seconds, complete 1024-input truth table and all witnesses verified.
- Matching-prefix K4 with 13 OR gates: SAT in 0.257 seconds, likewise fully verified.

UNSAT is a Z3 result, not a kernel-checked certificate. Both SAT models meet rather than violate the relevant lower bound and are positive controls. The matching-prefix UNSAT result excludes only that restricted gadget. The general timeouts exclude nothing.

Commands: `python3 or-synth-incidence.py k4-incidence.json 10 180000`; `python3 or-synth-incidence-gadget.py k4-incidence.json 10 180000 matchingprefix`. Python with Z3 5.3.3 is used; no solver binary is bundled. Adjacent independent OR gates are canonically ordered, with the prefix boundary exempted. All exact SMT assertions are included. The earlier frozen search validation gives the Z3 source and installation details.

An independent antichain implementation in `score-counterexample-q5-independent.py` verified the saved model and all hypotheses, and additionally checked OutputTopForm: all AND gates except the final output accept a singleton, while the output AND has no readers. Its complete log is included.
