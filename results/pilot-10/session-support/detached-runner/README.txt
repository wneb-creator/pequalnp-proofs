Detached build/checker runner for pequalnp-pilot-10

Prepared during the no-lease interval. No build or checker was launched to test it.
Python AST parsing, runner --help, and bash -n command.sh passed. Full validation
outputs are runner-help.* and driver-syntax.*; validation.json records hashes.

For an authorized proof after the root has renewed its lease, replace XXXX:

python3 /tmp/oec/pequalnp-pilot-10/toolchain/detached/runner.py launch --kind build --source /workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_XXXX.lean --run-dir /tmp/oec/pequalnp-pilot-10/detached-runs/metaXXXX-build-1

python3 /tmp/oec/pequalnp-pilot-10/toolchain/detached/runner.py launch --kind checker --source /workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_XXXX.lean --statement /tmp/oec/pequalnp-pilot-10/statement-meta-XXXX.txt --run-dir /tmp/oec/pequalnp-pilot-10/detached-runs/metaXXXX-checker-1

Use a fresh run directory each time; existing directories are refused. The launch
prints only the worker PID/PGID and run directory. It creates a detached worker
session, then a separate command process group. The command driver sources the
existing environment.sh and uses an explicit workdir. The commands are ordinary
lake build <module> or node tools/check-lean.mjs <source> <statement> check.
The normal queue, checker, configurations, binaries and internal timeouts remain
unchanged. There is no arbitrary-command option and no environment dump.

Status:
python3 /tmp/oec/pequalnp-pilot-10/toolchain/detached/runner.py status --run-dir /tmp/oec/pequalnp-pilot-10/detached-runs/metaXXXX-build-1

Graceful cancellation, only after the root decides to stop that particular run:
python3 /tmp/oec/pequalnp-pilot-10/toolchain/detached/runner.py cancel --run-dir /tmp/oec/pequalnp-pilot-10/detached-runs/metaXXXX-build-1

Cancellation rechecks the live command PID, /proc start time and process group,
then sends SIGINT to that group. It never escalates to SIGKILL. The separate
worker remains waiting so it can preserve the command's actual exit status.
If process identity cannot be verified, cancellation refuses without signaling.

Per-run files:
- spec.json and source.sha256: exact source identity before launch; statement
  identity is also captured for checker runs. The worker rechecks these hashes
  immediately before starting the command.
- stdout and stderr: complete command output, written directly to files.
- runner.stdout and runner.stderr: complete worker diagnostics.
- launch.json and running.json: worker/command PID, PGID and start metadata.
- result.json and status: observed command return code, elapsed time and final
  source/statement hash comparison. status is written only after observed wait.
- cancel-request.json: an explicit SIGINT request, if any.
- runner-error.json: infrastructure exceptions; these are not proof verdicts.

Limits: a detached session and ignored SIGHUP should survive ordinary exec/PTY
disconnects. They cannot survive host teardown, OOM/SIGKILL, platform-wide process
cleanup or deletion of the scratch filesystem. Missing result/status never means
success. Existing build/checker locks may need separately verified stale cleanup
after a real process loss. The runner does not clean locks, restart failed jobs,
renew a lease, extend the checker timeout, or make any proof-acceptance claim.
Do not change the proof or statement while a run is active; a changed hash is
reported even if the command itself returned zero.
