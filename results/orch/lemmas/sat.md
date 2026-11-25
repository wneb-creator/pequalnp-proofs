# SAT decomposition notes for L-meta-1479

Owner: sat_decomposition. Root alone holds the lease, commits, pushes, and submits.

## Current result

No circuit meeting the posted 27-gate double re-read target has been found. All UNSAT results below are computational results from CaDiCaL, not Lean-checked certificates. UNKNOWN means the allotted run was stopped or timed out; it is not evidence of impossibility.

## Encoding and validation

The solver is bundled with Lean at `/tmp/oec/pequalnp-pilot-81/lean-4.36.0-linux/bin/cadical`.

A circuit is constrained to binary AND/OR gates on distinct earlier wires. Correctness is tested on every minimal true edge assignment and every maximal false assignment; monotonicity makes this sufficient for the whole graph function. Where requested, two extra singleton rows and the exact product-rule derivative recurrences impose double quietness. Every SAT witness is independently evaluated on all Boolean inputs and both traces before being reported.

Canonical ordering of gates by (larger operand, smaller operand) removes topological permutations. A greedy ordering of available gates proves this is available for every DAG: newly available gates use the just-created wire and therefore have a larger maximum operand. Optional operation ordering puts AND before OR for an identical operand pair. Unused non-output gates may be deleted; the bounded searches request useful exact-size circuits.

The positive-edge-support restriction is optional and off by default. Root's team has now Lean-checked the full Fano normalization: replace a gate that is false on every positive edge by the AND of a different incident edge from the marked one. This preserves gate count, distinct inputs, correctness, and both marked traces without deleting or redirecting wires. The same mathematical argument applies to the local graph targets, but their specialized Lean statements are not supplied here. Crucially, a supported-gate restriction in a frozen-scaffold search remains a restricted model, because normalization could change frozen gates.

## Completed searches

| Search | Result |
|---|---|
| One three-leaf star, 3 ordinary gates | SAT; exhaustive truth check passed |
| One three-leaf star, 5 gates with double quiet | SAT; exhaustive truth and trace checks passed |
| Two stars, 7 gates, shared marked incidence | UNSAT in 0.99 seconds |
| Two stars, 7 gates, private marked incidence | UNSAT in 2.21 seconds |
| Three stars, 11 gates: collinear/noncollinear and shared/private incidence cases | Four runs UNKNOWN after 300 seconds each |
| Ordered three-star variants and full-Fano joint H,N at 24 gates | UNKNOWN after 300 seconds each |
| Full Fano, 27 gates, final AND with singleton supports empty/empty, 1-by-1, or 1-by-2 | UNKNOWN after 300 seconds each |
| Verified 28-gate Fano scaffold, delete one gate and free a radius-two positional window | 27 UNSAT cases, 1 UNKNOWN |
| Same scaffold, free a one-hop dependency cone | 20 UNSAT cases, 8 UNKNOWN |
| Same scaffold, radius-three window with support restriction | 23 UNSAT cases, 5 UNKNOWN |
| Four-cap 16-gate scaffold, delete one gate and free a radius-two window | All 16 cases UNSAT, without support restriction |
| Same four-cap scaffold, free a one-hop dependency cone | All 16 cases UNSAT, without support restriction |

The repair encoder's positive controls recovered ordinary 27-gate Fano and ordinary 15-gate four-cap circuits in 0.068 and 0.081 seconds. All inputs were checked; both marked derivatives were true, so these controls are explicitly not target witnesses.

The longer ordered noncollinear three-star/shared-incidence run began at 09:57:21 UTC and was stopped on root's instruction at 10:04:52, UNKNOWN after 452.163 seconds. Root redirected because a shared marked incidence admits a plausible sequential private-leaf elimination to C6 with at most eight gates and repeated operands. The constructive agent independently found that relaxed C6 case UNSAT. This transfer is not Lean-certified. It does not cover a marked private leaf: that leaf must remain, giving C6 plus one leaf with at most nine gates instead.

## Retired joint-output route

The fixed-prefix joint H,N12 run began at 10:10:31 UTC and stopped UNKNOWN at 10:24:25 after 833.755 seconds. Its nine-essential-input-clause variant began immediately afterward and stopped UNKNOWN at 10:30:35 after 370.894 seconds. Both complete logs are preserved. The variant was independently reviewed: its nine finite comparison certificates are valid, and the known13 control satisfies all14,666 clauses.

The reason for retiring this route is an upstream checked result, not a conclusion from these timeouts. The full H,N24 child L-meta-6658 was refuted by checked negation L-meta-6659 in accepted PR13206 at about10:13:54 UTC, making R_meta_1479_824 dead. A local H,N12 witness would append three stars and three ORs to give that impossible full H,N24 witness. Reference: https://github.com/open-goat/pequalnp-proofs/pull/13206 .

## Active broad full-Fano search

Started approximately 2026-11-25 10:34 UTC after root renewed the lease at10:34:16 (expiry10:54:16; automatic ten-minute renewals continue). This is the sole SAT worker, with a7,200-second cap.

The unrestricted full-Fano27 encoding uses14 inputs,60 truth rows (21 minimal positives,37 maximal negatives,and2 marked singleton bases),exactly27 binary AND/OR gates,6,669 variables,and195,917 clauses. It enforces distinct backward operands,exact formal derivatives at marked flag(0,0),every gate used,every primary input read,positive support,and canonical gate-pair/operator ordering. No prefix or final-gate operator is fixed.

Independent review passed at10:33:36. The canonical28 control assigns all6,944 variables and satisfies all208,842 clauses under the identical restrictions. The reviewer also checked all16,384 truth assignments,both derivatives,the primitive CNF relations,and all21 flag symmetries. Its report is status-full-fano-sat-review.txt. This validates the encoding,not satisfiability at27.

Exact-size completeness uses output-operator padding after deleting dead gates: if the current root is AND(a,b),append AND(output,a); if OR(a,b),append OR(output,a). The value and both zero marked derivatives remain unchanged,operands remain distinct,and all gates stay useful. Positive support is justified by the team's compiled normalization theorem. These analytic completeness checks and the separate Lean support theorem do not make a future solver UNSAT a Lean refutation; that would require a checked certificate.

Active scratch prefix: sat-fano-full27-broad, with complete .cnf,.metadata.json,.stdout,.stderr,and.runlog files. Any SAT candidate is exhaustively checked on all16,384 inputs and both traces before a witness JSON is written.

## Reviewed minimal-boundary restart

The initial unrestricted full27 run stopped UNKNOWN at10:44:39 UTC after590.05 seconds (exit-15). Its complete CNF,metadata,stdout,stderr,andrunlog are archived losslessly under sat-archive.

The sole replacement worker started at10:44:41 UTC with6,555seconds remaining until the original12:34deadline. Root renewed at10:42:24,expiry11:02:23.875; automatic renewals continue. Source sat-fano-minimal.py adds sound ordinary-minimality constraints using the accepted Fano lowerbound27: AND operands must be incomparable on maximal-negative rows,OR operands on minimal-positive rows,and every gate must be false on some maximal-negative row. A violating gate could be replaced by an operand or virtualtrue, preserving the relevant boundary and moving the other boundary toward correctness. Function-only alias/constant cleanup then gives a strict circuit with at most26 gates,contradicting the accepted lowerbound. Trace preservation is not needed for this contradiction.

Independent audits passed for every extension. The final known28control assigns all10,192 variables and satisfies all218,726 clauses. This concrete28control check is not a general completeness claim at28; minimality cuts are justified for27. Final target model:9,801variables,205,448clauses. Active prefix sat-fano-minimal27-broad. Its immutable CNF/metadata are archived; live complete solver logs remain in scratch until completion. No prefix or final-gate operation is fixed,and no global Bzero=0 restriction is imposed.

## Artifacts

Source snapshots in this folder: `sat-local.py`, `sat-hn.py`, `sat-hn-essential.py`, `sat-topfactor.py`, `sat-repair.py`, and `sat-fano-full.py`. Seed files: `sat-seed28.json` and `sat-fourcap-seed16.json`. Scripts expect the scratch root `/tmp/oec/pequalnp-pilot-81`; restore `sat-seed28.json` there as `stochastic28-compact.json`.

All generated CNF files and complete solver stdout/stderr remain under the scratch root, together with JSON-line run logs recording each exact case and its result. No credentials are read by these scripts. The machine exposes five logical CPUs; only one SAT worker is active after the initial exploratory batches.

10:18 UTC independent review: lean_setup generated the H/N13 control CNF from the actual encoder under the same ordering and support constraints, assigned all 924 variables using the known canonical circuit, and checked all 14,657 clauses. It also verified all 512 H/N inputs and the corresponding 28-gate full-Fano splice on all 16,384 inputs and both derivatives. No extra solver ran. The review report and source hashes are in sat-joint12-independent-review.json. This validates the encoder/validator; it is not a target witness.
