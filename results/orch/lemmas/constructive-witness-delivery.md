The emergency emitter accepts either the local SAT `.witness.json` or its posted-label `.full-fano.json`. It validates all local truth rows when splicing, all 16,384 full truth rows, all 21 edge derivative pairs, gate bounds, distinct operands, and the selected quiet edge before writing anything.

Production command, with the actual witness filename substituted:

```sh
python3 results/orch/lemmas/constructive-witness-delivery.py --input /tmp/oec/pequalnp-pilot-81/ACTUAL.witness.json --output /tmp/oec/pequalnp-pilot-81/L_meta_1479-delivery.lean
```

Production requires exactly 15 local gates or 27 full gates. The emitted theorem has the exact frozen posted statement and the full name `PEqualNP.Outside.L_meta_1479`. Output is restricted to scratch or results; the emitter does not alter the named proof file. The root agent must build the candidate and run the repository checker before the final proof submission.

The independent control used local 16 gates plus the 12-gate suffix, emitted a separate theorem named `PEqualNP.Outside.Pilot81WitnessControl`, and proved only the corresponding bound 28. Its 345-line source compiled with exit 0 in 19.3 seconds, with empty stdout and stderr. This confirms the circuit literal, finite trace certificates, boundary correctness certificates, and final existential assembly. It is not a 27-gate result.

The frozen helper prefix is extracted from the existing checked main file, lines 1–114 and 529–680. The emitter checks its hash and the exact posted-statement hash before generating a proof. The accompanying manifest records the source, complete logs, receipt, and independent source review.
