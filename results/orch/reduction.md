# Reduction strategy for L-meta-2592

2026-11-25 initial inspection: the public feed lists three open reductions for L-meta-2592, matching `reductions_live: 3`. The join rules cap reductions at three per step, so a fourth reduction cannot currently be submitted.

Existing reductions:
- `R_meta_2592_271`: arbitrary fan-in-two Petersen circuit needs at least `15 + notCount C` gates; then exclude 1 through 4 NOT gates under total size 19. The binary-count half is already checked in `L_meta_4725.lean` (3224 lines); remaining child is `L-meta-4727`.
- `R_meta_2592_318`: split at the last NOT into arbitrary prefix P and monotone suffix Q, with size sum plus one; then exclude all such separators with combined size at most 18. Factorization is already checked in `L_meta_8295.lean` (66 lines); separator child `L-meta-8297` is open.
- `R_meta_2592_408`: normalize invalid wire reads, unused NOT operands, and output trimming; then exclude normalized circuits of size at most 19 (strictly below 19 or containing NOT). Remaining normalized bound child `L-meta-7391` is open.

The exact negated twin `L-meta-2593` is currently posted. Root alone controls lease/submission decisions.

Child `L-meta-4727` already has reductions into truth-function synthesis (`R_meta_4727_17`) and signed BinaryCircuit synthesis (`R_meta_4727_53`). Their hard halves are exact finite search bounds, with algebraic compilation separated out.

## SAT route

Built CaDiCaL from the public GitHub source under scratch. Binary: `/tmp/oec/pequalnp-pilot-100/sat/cadical/build/cadical`.

The existing generator `notes/data/lrat-link/gennot.py` mirrors the checked FanInTwo LRAT encoding. The full Petersen 19-slot, 1024-row formula has 211000 DIMACS variables, 1429441 clauses, about32MB. Boundary rows alone comprise15 minimal true rows and15 maximal false rows; they do not constrain negated circuits enough:
-19 slots on30 boundary rows: SAT, decoded circuit fails864 of1024 full truth-table rows.
-17 slots on30 boundary rows: SAT, decoded circuit fails826 rows.

The17-slot run used textual LRAT. Because it ended SAT, its359763742-byte trace was not an UNSAT certificate and was deleted after recording its size and SHA256 in scratch. Complete stdout/stderr remain. All later runs disable proof dumping until an UNSAT case is found and judged affordable.

A second19-slot CEGAR round uses86 rows: all inputs of weight0,1,2; all ones; the original boundary rows; and representative failures of weights3 through9. No result yet.

`results/orch/lemmas/SatBase.lean` is an uncompiled, isolated copy of the LRAT kernel and FanInTwo soundness chain, plus necessary Shannon helpers. It imports only PEqualNP.Defs. Forbidden local tactic macros were expanded; comments removed; namespaces renamed under PEqualNP.Outside.L_meta_2592_aux. It is about100KB before certificates. The original Trie inductive/model structures/Decidable instance remain and would need the manual-review path if used in a final proof without further refactoring.

SatBase compilation PASSED (exit0). Complete logs copied to results/orch/validation/SatBase.stdout.txt and SatBase.stderr.txt; concise scope/limitations in SatBase.txt. It is a checked conditional bridge, not the full gap.

The19-slot86-row and17-slot86-row CEGAR searches both timed out UNKNOWN at240seconds. A20minute global19-slot search now runs all1024 rows, firstgateOR(0,2), and1..3NOT gates. Another CNF adds onehot operation/source choices plus a disjunction of some primaryinput being read once, with noAND/OR primary co-reader for that input. It does not forbid a soleNOT reader, because laterNOTs can restore polarity. These extra constraints are only used for witness search unless preservation is separately proved.

Independent review of root ReadCount.lean: PASS for helper preservation. The19-gate counting contradiction keeps all required assumptions explicit: all10 inputs occur, allg-1 earlier internalwires occur, and at least one gate has at most one listed operand. `slots` counts even ignored NOT operands, so a normalized unaryNOT hypothesis is needed. No unstated semantic normalizer is inferred. Text scan clean.

Independent canonical seed verification: the phase seed violates exactly5 clauses of the full leaf-constrained CNF:4 wrong-output rows69,208,276,385, plus usage of deadNOT wire22. All18945 added leaf/onehot clauses hold, and primary once-read inputs are1,3,5,9. This matches the counterexample-search agent's intended seed, not a valid circuit.

2026-11-25T14:19:19Z: root requested CPU priority for the long DeletedSigned kernel compilation. The unseeded globalSAT processPID6206 was stopped withSIGSTOP and its stopped state verified. No SAT or UNSAT result was produced. Native wall-clock timeout may expire while stopped, so resumption may finish as UNKNOWN; complete stdout/stderr are retained. No proof trace exists for this run.
