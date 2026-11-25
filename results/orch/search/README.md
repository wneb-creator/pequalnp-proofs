# L-meta-2592 computational search

No valid circuit with at most 19 gates has been found. These files are research
artifacts, not a Lean proof of the posted statement or its negation.

`near-candidate-19.json` records a 19-gate monotone circuit computing the Petersen
edge function with the extra edge {3,9}. It fails exactly on input masks 520, 521,
522, 552 and 554. Its truth table was checked on all 1,024 inputs. It is not a
counterexample to the posted statement.

The first stochastic search made 1,467,814,678 full truth-table evaluations across
14,678 restarts. Its best result was the five-error circuit above. The local
four-gate repair search and the coordinated deletion/negation searches found no
repair. `delete-two.log` records 183,416,922 configurations obtained from the 40
known 20-gate constructions; none passed even the 32 critical inputs.

The two SAT models in `not1-model-0.json` and `not4-model-0.json` match only the
initial 30 boundary rows. They fail 870 and 410 of the full inputs respectively.
They are retained to document why boundary rows are insufficient for circuits
with NOT gates. The completed longer synthesis runs retained here returned
UNKNOWN at their time limits; UNKNOWN is not an exclusion proof.

`signed_source.py` generates the shared-negated-source SAT encoding and checks
decoded models on all 1,024 inputs. Two fixed-circuit smoke tests passed, including
an actual negative use of the false source and expansion to ordinary NOT gates.
`build_signed_cases.py OUTPUT_DIRECTORY` regenerates the principal strengthened
instances, without network calls or running a solver. The extra reader and
proper-gate restrictions are search assumptions derived from the proof work;
these CNFs are not themselves certified exhaustive lower bounds.

`manifest.json` contains SHA256 hashes for preserved source files and complete
completed-run logs. Large CNFs remain in scratch and can be regenerated. The
ongoing hour-long run is recorded separately in scratch by
`signed2-long-nor01.status.json`; its final log will be added when it finishes.
