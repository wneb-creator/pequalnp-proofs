# Independent review records

## Finite-search artifacts

The initial 38-file manifest and the subsequent frozen 78-file manifest both had exact file coverage and matching SHA256 hashes. All seven graph datasets and their critical rows were independently regenerated. The 1197 logged BFS witnesses were independently evaluated on complete truth tables and their ownership profiles recomputed. No credential, environment-dump, network-call, or destructive-code findings were identified in the preserved search sources and logs. Solver banner URLs are metadata.

The frozen 78-file update correctly labels the interrupted theta233, theta333, and C6 shared-OR runs UNKNOWN_INTERRUPTED. Their full solver and wrapper logs contain no final status. The recorded C6 seven-gate UNSAT result is a separate completed run.

## Direct circuit CNF

Reviewed source synth_sat.py SHA256: 5d0e834ff59c4138e7a3feb6b0a163d80faf2817bbe5291908c8ebe42cab70c3.

All 16 local gate truth assignments were checked against the gate clauses. Four generated models had matching CNF hashes, variable/clause counts, and exact edge-plus-maximal-independent-set rows. The C5 seven-gate SAT assignment satisfies every CNF clause, and its decoded circuit agrees with the graph function on all 32 inputs.

The model uses exactly K binary gates, distinct ordered operands, every primary input mentioned, and a final-gate output. Constant/alias simplification, pruning, commutativity, and unused-copy padding justify these restrictions for minimum circuits of the studied nonconstant graphs without isolated vertices. This normalization argument is informal here. No additional depth ordering was enabled in the reported SAT queries.

## Shared pure-OR CNF

Reviewed source synth_sat_shared.py SHA256: d0a3114c840b23a0c231737a5912b6bcc991a07f6292a9ae01583b6f5a00dfda.

The C5/C6 models use all 32/64 input rows and enumerate all 130/342 eligible gate/support choices. The chosen gate is OR, its full truth table is the disjunction of a subset of at least two primary inputs, and at least two distinct later gates read it. Distinct operands ensure two selector occurrences cannot come from one parent. Every nonfinal gate feeds a later gate, which implies every gate lies in the final output cone.

## AND-count search with OR free

Reviewed source free_or_sat.py SHA256: ca33829e0d047e59bda013f381278977dfc4a9a2cbc1c6477a521efe3044f7a4.

The encoding allows at most k AND gates. Each operand is an arbitrary disjunction of primaries and earlier AND outputs; the output is an arbitrary disjunction of AND outputs. The Tseitin clauses and critical rows are correct. The C7 four-AND SAT model was independently checked against all 1351 CNF clauses, and both its collapsed representation and its concrete 16-gate binary realization were checked on all 128 inputs.

Informal completeness follows by eliminating constants and aliases, collapsing each OR cone into its contributing primaries and earlier AND outputs, and omitting primary output terms because graph edge functions are false on singletons. Unused AND slots may compute false. C7 with three ANDs returned UNSAT; Petersen with five ANDs returned no status at its 120-second limit and remains UNKNOWN.

All solver UNSAT reports are computational evidence about the encoding, not Lean-checked lower-bound theorems. This review does not cover the later free_or_dual_sat.py or free_or_disjoint_sat.py variants.
