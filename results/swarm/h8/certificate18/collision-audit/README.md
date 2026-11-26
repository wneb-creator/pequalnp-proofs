# Portable packed-collision audit

This package compares the 419-bit packed collision algorithm with the original scalar row checks on five fixed search nodes. It uses Python 3 and its standard library. No Lean installation, network access, repository checkout, or full wire database is needed to rerun the audit.

From this directory:

```sh
python3 audit_packed_collision.py --fixture fixture.json --output report.json > run.stdout 2> run.stderr
```

The supplied run passes all 7,338 eligible ordered operand/operator/keep choices: 5,284 collision cuts and 2,054 noncuts. It also compares 2,552 computed gate signatures with signatures obtained directly from the 419 row pairs.

| Node | Parent width | Cap | Eligible children | Collision cuts | Noncuts |
|---:|---:|---:|---:|---:|---:|
| 0 | 10 | 17 | 1,440 | 1,080 | 360 |
| 52 | 13 | 14 | 2,328 | 1,376 | 952 |
| 292 | 10 | 13 | 1,440 | 1,058 | 382 |
| 522 | 13 | 13 | 1,770 | 1,412 | 358 |
| 5229 | 10 | 9 | 360 | 358 | 2 |

`fixture.json` contains the exact 419 ordered Extended-row pairs, the 1024-bit target word, and the complete parent banks/caps for these nodes. Each hexadecimal word has 256 digits; bit r gives the value on Extended row r. No external file is consulted during the audit.

Native row bit i maps to Extended row bit `[9,7,5,8,6,4,2,0,3,1][i]`. Fixture extraction checked this formula against all 1,024 entries of the original forward mapping and its inverse. Native wire records contain 128 little-endian truth bytes followed by four int32 origin fields. Source paths, byte counts, SHA-256 digests, pair packing, and row mapping provenance are recorded under `fixture.json`'s `provenance` field and copied into `report.json`.

All 419 pairs must separate the target. The audit validates that prerequisite and checks that a synthetic equal-row pair violates it. For each eligible child, packed coverage is compared both with the scalar check after the original parent profile filter and with the scalar check over all 419 pairs. Operators are 0=AND, 1=OR, 2=ANDNOT, 3=NOTAND. The child eligibility rules and child order match the original audit.

Only input/output plumbing changed in the portable audit. `io-refactor.diff` records the change; `io-refactor-audit.json` confirms identical parsed Python syntax trees for the three algorithm functions and the complete ordered gate/keep enumeration loop. The frozen expected per-node results are also checked on every rerun. Assertions must remain enabled; use the command above without Python optimization flags.

`run.stdout` and `run.stderr` are complete logs. `report.json` records the result and elapsed time. `SHA256SUMS` covers every other package file; rerunning the audit changes elapsed-time-dependent report/log hashes.

For provenance reconstruction only, `make_fixture.py` can rebuild the fixture from the original frozen source tree:

```sh
python3 make_fixture.py --source-root /path/to/pnp-swarm-2373-8 --output fixture.json
```

This finite native comparison supports review of the packed algorithm. The Lean proof and whole-forest replay are separate evidence.
