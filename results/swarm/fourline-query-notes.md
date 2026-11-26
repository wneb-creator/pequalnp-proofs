Four-line query diversification, frozen encoder unchanged

Target q3fourline18-all.cnf/.json uses order3 lines0,1,4,8, all existing flags, and budget18. It has14inputs,16edges,16positive and16maximal-false rows,24verified input automorphisms,7027variables154162clauses. Target CNFSHAbf2052ead7edcd39b5249f1f0f4c6906c6506d85b18e5ec45b361b072f09403d.

Each selected line has4points. The10 covered points have degrees at most2, confirming no selected triple is concurrent. Canonical size is16edges+4stars-1=19. The remaining9line stars add exactly45gates including joins; a<=18gate core therefore extends to<=63full-plane gates. This is an additional sufficient construction for a refutation, not a characterization of all full-plane circuits. A coreUNSAT verdict would not prove L-meta-2583.

Control q3fourline20-control pins a canonical19gate circuit in budget20, with a duplicate-fanin inactive suffix gate. No SAT solver was invoked: audit_fourline_query.py directly constructs a complete Boolean assignment and checks every185887clause, every16384core input, all38selected whole-output bypass witnesses, every automorphism and group closure. The explicit model is q3fourline20-control-explicit-model.txt and is marked as independently constructed.

The unchanged decoder accepts this model, trims to19gates, and exhaustively checks16384inputs. The unchanged extension returns64gates and passes52positive/704maximal-false fullplane rows. Logs q3fourline20-control-decode.log and q3fourline-extension-control.log. Detailed audit fourline-query-audit.log/json. No target solver launched by the diversification task.

Generate command from /workspace/pequalnp-proofs (use a fresh output prefix):
```sh
python3 /tmp/oec/pnp-swarm-2583-orch/core_sat.py generate \
  --gates 18 --order 3 --line-ids '0,1,4,8' \
  --output /tmp/oec/pnp-swarm-2583-orch/q3fourline18-reproduced \
  --at-most --incomparable-operands --all-gates-pair-active \
  --all-active-gates-used --essential-inputs-used --order-independent-gates \
  --op-critical-domains --critical-output-witnesses --first-input-orbit \
  > /tmp/oec/pnp-swarm-2583-orch/q3fourline18-reproduced-generate.log 2>&1
```
