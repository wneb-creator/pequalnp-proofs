# P4 bridge compilation checkpoint

This preserves the exact generated 30-clause prototype that compiled in scratch as ReductionsBridge.lean. Its final goal is True. Thirty local clause-satisfaction proofs are typechecked inside it, but they are not yet exported as a useful encoding bridge. This is a compilation checkpoint, not a new lower-bound theorem or a proof of L-meta-2602.

The prototype contains a typed five-gate candidate, symbolic values for all 452 CNF variables, and assignment lookup lemmas. The symbolic reconstruction regenerates the certified 2537-clause CNF byte for byte. The full bridge and the comparison with ordinary gate/derivative evaluation remain in progress. It imports the separately preserved Reductions.lean concrete-CNF UNSAT control.

The source is reproducible using p4_bridge_generate.py followed by p4_bridge_lean.py --count 30. The archived source has been renamed ReductionsPrefix30.lean to keep it separate from the ongoing bridge. The complete compiler output is retained in gzip; it contains only unused-variable/tactic warnings.
