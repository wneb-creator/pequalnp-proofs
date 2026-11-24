# CaDiCaL 2.1.2 streaming compatibility: PASS without changes

The pushed `run_checked_kissat.py` works unchanged with the installed official
Lean CaDiCaL binary. Set its solver path to
`/tmp/oec/pequalnp-pilot-18/lean-4.36.0-linux/bin/cadical` and pass exactly
`--solver-arg=--unsat`. The runner invokes:

    cadical --unsat --no-color SNAPSHOT.cnf PROOF_FIFO

This binary accepts the runner's `--no-color` spelling, although its help
documents `--no-colors`. The final positional argument is the proof FIFO.
Default proof format is binary DRAT; the unchanged checker explicitly detected
that format in the controls. No adapter, proof conversion, `--force`, solver
source change, or checker change was needed.

Hash bindings:

- Runner: `535ff6e32a68a31eefa1545f031483d0e9b73acd79066d1bbb2a2f42c86685bb`
- CaDiCaL: `2a0137451efde370d67b88aec26f1e902870f095b1204b07049a103bc6bbd647`
- DSR checker: `e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b`

Example command, with caller-supplied fresh output and input hash:

    python3 /workspace/pequalnp-proofs/results/pilot-18/search/run_checked_kissat.py INSTANCE.cnf NEW_OUTPUT \
      --solver /tmp/oec/pequalnp-pilot-18/lean-4.36.0-linux/bin/cadical \
      --solver-arg=--unsat \
      --checker /tmp/oec/pequalnp-pilot-18/solver/dsr-trim/bin/dsr-trim \
      --checker-sha256 e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b \
      --cnf-sha256 EXPECTED_CNF_SHA256 \
      --solver-memory-mb 1500 --checker-memory-mb 3000 \
      --max-seconds 3600 --abort-file ABORT_SENTINEL

Use the runner's wall-time bound. CaDiCaL documents `-t SECONDS`, not Kissat's
`--time=SECONDS`; that short option pair is not accepted by the runner's option
allowlist. A runner time-limit abort remains an abort, not an UNSAT result.

## Controls

All controls used fresh scratch paths and the unchanged binaries and runner.

| Control | Solver result | Checker result | Raw proof bytes |
| --- | --- | --- | ---: |
| Contradictory unit clauses | UNSAT, exit 20 | VERIFIED UNSAT, exit 0 | 5 |
| Two-variable SAT formula | SAT, exit 10 | VALID, exit 0 | 0 |
| K4 with three colors | UNSAT, exit 20 | VERIFIED UNSAT, exit 0 | 50 |
| Seven pigeons into six holes | UNSAT, exit 20 | VERIFIED UNSAT, exit 0 | 14,870 |
| Six pigeons into six holes | SAT, exit 10 | VALID, exit 0 | 0 |

Each UNSAT runner result required both the exact solver verdict/exit 20 and
the explicit checker `s VERIFIED UNSAT`/exit 0, plus the complete hashed proof
stream. The two SAT assignments were independently checked against every
clause, but the runner correctly labels them `SAT_UNVALIDATED`, never UNSAT.

A separately captured 50-byte K4 control proof has exactly the same byte count
and SHA256 as its streamed proof, and also passes a direct checker invocation.
Replacing it with just a binary empty-clause claim is rejected (checker exit
1). This verifies that a proof is needed for the nontrivial control. Only this
tiny control proof is retained; real runs retain no replayable proof artifact.

Complete solver/checker and driver stdout/stderr, inputs, result JSONs, help,
version, commands and hashes are under `lean-setup/cadical-streaming-controls/`.
`cadical-streaming-review.json` binds all artifacts. Test driver source is
`lean-setup/test_cadical_streaming.py`.

The existing default-width DSR safety limits and proof-retention limits still
apply. These subsecond controls do not predict production memory or runtime.
Do not switch to LRAT/IDRUP/LIDRUP or embedded DIMACS option overrides for this
recipe. No active worker, running CNF, lease, or repository file was changed.
No assigned search case was solved, and no Lean acceptance is claimed.
