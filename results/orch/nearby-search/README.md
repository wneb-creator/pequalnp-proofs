# Bounded repair of invalid near-miss circuits

The two near-3 JSON files are INVALID circuits. Each fails three positive edge tests. They are seeds for a bounded edit search, not counterexamples or proofs. No nearby repair solver had been run at snapshot time.

SearchNearby.py takes a general binary synthesis CNF and adds a maximum edit distance from a supplied seed: changing one ordered fan-in costs1, and changing one gate operation costs1. A unary counter enforces the bound. Optional --pad appends copies of the final gate operation applied to its own result and one previous operand; absorption preserves the seed function. All accepted SAT models must still satisfy the original complete-test circuit constraints, and SearchDecode.py checks the decoded circuit independently on all24positive+64negative assignments.

Validation: the signed-literal counter passed1280 complete truth assignments for budgets0..4. A known correct29-gate circuit satisfies all510628 baseline clauses and438 additional zero-edit clauses. The counter/padding source was independently reviewed. The only change to Search.py from reviewedv3 is an explicit --statement path parameter, allowing reproduction from the saved posted statement.

Example generation, run from repository root:
```
python3 results/orch/nearby-search/Search.py --case plane_local --points '0,1,2,3,8,15' --statement results/orch/nearby-search/statement.txt --gates 28 --no-ordering --no-pruning --no-incomparability --output /tmp/oec/pequalnp-pilot-29/nearby-base28.cnf
python3 results/orch/nearby-search/SearchNearby.py --cnf /tmp/oec/pequalnp-pilot-29/nearby-base28.cnf --nearby results/orch/nearby-search/near-3-7.json --edits 4 --pad --output /tmp/oec/pequalnp-pilot-29/nearby-seed7-edits4.cnf
```

These settings leave gate ordering and minimality restrictions disabled, avoiding any conflict with the supplied seed's serialization. The synthesis model still uses strict backward binary gates and requires all gates in the output cone. A timeout or UNSAT result for a bounded neighborhood does not prove a global lower bound.
