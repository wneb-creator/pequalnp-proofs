# Petersen 19-gate heuristic search, version 1

This frozen run ended UNKNOWN. It recorded no correct circuit and proves no lower bound or refutation of L-meta-1772.

The exact script, complete stdout/stderr log, best candidate, and replay encoding are preserved here. The script SHA256 is `3b70efc5488197512f390237c79e6d0b503818ff773a721aea3f8a5b123a6290`. The encoding was copied byte-for-byte from the actual input `sat-petersen19restartbase-19-encoding.json`.

## Recorded result

- Seed: 66; requested duration: 600 seconds.
- Completed: 172,795,000 iterations and 8,640 restarts; measured duration 600.000660873 seconds.
- Best candidate: 19 legal binary monotone gates, but one scored test error and nine full truth-table errors among 1,024 inputs.
- Candidate status: `HEURISTIC_CANDIDATE_NOT_A_CORRECT_CIRCUIT`.

`validation.json` records an independent reevaluation of the archived candidate and encoding. The 30 scored tests are exactly the 15 edge inputs and the 15 maximal independent inputs. For a monotone circuit, passing all these tests would characterize the graph function. The script additionally asserts equality on all 1,024 inputs before labeling a zero-score candidate an exact truth-table witness. No zero-score candidate was recorded. Even such a witness would require separate Lean checking and would not automatically refute the ownership statement.

## Search model and limitations

The script starts from random minimum-vertex-cover star constructions, contracts gates to reach 19 gates, and mutates binary AND/OR gates using earlier wires. The output is the final gate. Duplicate operands and unused gates are allowed. The annealing search is finite and not exhaustive; a timeout or positive best score is always UNKNOWN, never UNSAT or an optimality claim.

Independent review found one search-quality bug: an improvement accepted by the final mutation of an inner round can be discarded at restart before the next best/save check. A zero-score candidate at that boundary could therefore be missed. This cannot create a false witness. The archived version is unchanged; a later version fixes that boundary, but its changing run is not included here.

## Replay

From this directory, using Python 3 and only its standard library:

```sh
python3 rewire_search.py --encoding petersen19-encoding.json --seconds 600 --seed 66 --output /tmp/oec/pequalnp-pilot-66/heuristic-replay-best.json
```

The stopping iteration and elapsed times depend on machine speed. No solver binary, credentials, or installation files are included. `sha256.json` hashes every other file in this archive.
