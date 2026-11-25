# Fano single-core SAT search

Encoder: `/tmp/oec/pequalnp-pilot-71/structural/fano_sat.py`. Independent decoder: `decode_sat.py` in the same folder. CaDiCaL at the installed Lean toolchain bin/cadical; documented `-t 300` wall limit used. All stdout/stderr and witness outputs saved under structural/.

Encoding: 14 Fano inputs, AO2 choices with commutative operand ordering, all nonroot gates used later, root AND, root false on all 37 maximal independent sets, root accepted-edge cardinality, exact READ1 singleton/pair recurrence, one accepted edge lacking READ1, one root operand true on some maximal independent set. For fixed support, every listed input is used and no other input is allowed. Exact support of size equal to number of gates yields one repeated wire; explicit onehot repeated-wire and fanout-at-most-two clauses strengthen this.

Target: selected residual vertex cover Y satisfies all unaccepted edges. For g gates, q accepted edges, require q+7 > g+1+card Y. Encoded as cardinality q+(14-card Y)>=g+9. This is the exact target violation for one maximal core with the whole circuit as its cone. Appending an independent canonical exact graph circuit supplies a lift-fixed output without altering the dead core.

Validation: positive calibration (4-gate P4 core, no violation requirement) returned SAT; decoded circuit checked against every CNF clause and independent full truth-table evaluator.py.

Finished so far:
- S2975={0,1,2,3,4,7,8,9,11}, g9, accept all10 induced edges: UNSAT exit20,75.96sec.
- S959={0,1,2,3,4,5,7,8,9}, g9, accept>=9 with exact target: UNSAT exit20,48.88sec.

Ongoing: S1951,S1967,S1979,S2975 general9-edge-or-more target cases. A separate initial S2975 run forced repeated edge(0,7); it is only a restricted test because fixed-support stabilizers are not edge-transitive. The replacement S2975 uses an existential repeated edge and includes the fanout strengthening.

No SAT result is being described as a Lean theorem. UNSAT outcomes are computational search evidence only.

Further completed: S1951 UNSAT154.08sec (minimum8, therefore covers all necessaryq>=9); S1967 UNSAT50.08sec; S1979 UNSAT58.59sec. Initial biasedS2975 timedout300sec, no verdict.

Remaining S2975 has10inducededges. Caseacceptall10 alreadyUNSAT; exactly9accepted can be split by omitted-edge orbit. Representatives(0,7),(0,11),(1,7). Short-edge omission(1,7) UNSAT38.48sec; outer/inner stillrunning. General existential-repeatS2975 also running.

All five necessary support orbits for a 9-gate single-core Fano violation now returned UNSAT. General S2975 finished187.05seconds; its omitted outer/inner splits also returnedUNSAT53.70/43.42seconds. Summary with CNF hashes: structural/fano-sat-summary.json. This is a complete computational search under the independently enumerated support/orbit reductions, NOT a Lean proof.

Important search-direction update: every one-edge omission from S2975 raises residual tau from4to5. Thus a 10-gate/9-input violation must accept the full induced graph on each relevant support. For genuine higher-support flexibility with two extra fanout uses, next promising case is11gates/10inputs on S3007 (12inducededges).
