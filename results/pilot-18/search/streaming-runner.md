# Online certificate runner: feasible, with measured controls

`run_checked_kissat.py` is a standalone Python supervisor. It makes no desk call
and starts no background work until explicitly invoked. It runs unchanged Kissat
and an explicitly hash-pinned, unchanged DSR binary on the same copied CNF.

```sh
python3 /tmp/oec/pequalnp-pilot-18/lean-setup/run_checked_kissat.py \
  /absolute/path/case.cnf /absolute/path/NEW-run-directory \
  --solver /tmp/oec/pequalnp-pilot-18/solver/kissat-4.0.4-linux-amd64 \
  --checker /tmp/oec/pequalnp-pilot-18/solver/dsr-trim/bin/dsr-trim \
  --checker-sha256 e6894b5b74ac2c09b494344f397ec5111547aaa782cdb399f1a8b6835ecef84b \
  --solver-arg=--seed=17 --max-seconds 3600 \
  --abort-file /absolute/path/stop-request
```

Use a fresh output directory each time. An optional `--cnf-sha256` checks the
expected instance hash. The solver option interface accepts numeric/Boolean
long options and known presets; it cannot introduce positional proof files,
compressed outputs, or ASCII-proof overrides. No shell command is constructed.

## Acceptance and retained evidence

Exit 0 and `accepted_CNF_UNSAT=true` require **all** of:

- Solver exit 20 and exactly `s UNSATISFIABLE` in its separate stdout log.
- Checker exit 0 and exactly `s VERIFIED UNSAT` in its stdout log.
- Complete producer stream drained and hashed, unchanged CNF and executable
  hashes, and no abort, timeout, resource guard, or relay failure.

Solver SAT is exit 10 / `SAT_UNVALIDATED`; UNKNOWN is exit 2. Their models or
incomplete proofs are not accepted as UNSAT. Abort is exit 3; other failure is
exit 1. In particular, checker exit 0 with `s VALID` never establishes UNSAT.

The new directory retains the CNF snapshot, four complete stdout/stderr logs,
atomic progress/final JSON, byte counts, proof SHA-256, input/binary/log hashes,
exit codes, explicit verdicts, and resource measurements. It retains no raw or
compressed proof file. A proof digest is **not a replayable certificate**; a later
independent proof check requires rerunning the solver. Online CNF checking is
also not a Lean proof or posted-gap acceptance.

DSR may exit after proving an empty-clause prefix. On that explicit successful
exit, the runner drains and hashes the remainder of the solver's FIFO output
without forwarding more bytes. It records forwarded and unforwarded counts;
it does not claim that the checker consumed the entire tail. A verified prefix
already establishes CNF UNSAT, but the solver must still finish with exit 20.

## FIFO, cancellation, and storage

The private FIFO is opened nonblocking before either worker starts. A temporary
writer descriptor suppresses startup EOF until the solver exits. A bounded
1 MiB user-space relay plus kernel pipe buffers provide backpressure: a slow
checker slows the producer instead of accumulating a proof on disk. Solver and
checker logs are direct, separate file descriptors, never mixed with proof bytes.

Early checker failure terminates the solver; unexpected solver failure terminates
the checker. SIGINT/SIGTERM, wall timeout, low disk space, and the external abort
file terminate both private process groups, escalate to SIGKILL after a grace
period, reap children, and remove the FIFO. A Linux parent-death signal also kills
both direct workers if the supervisor itself is killed. A SIGKILL/environment
loss cannot produce a final report or run FIFO cleanup; any surviving progress
record is explicitly incomplete, and a leftover FIFO contains no stored proof.

The coordinator must create `--abort-file` on lease renewal failure/loss. The
runner checks its existence every loop and never reads its contents. It does not
renew leases, inspect lease identifiers, or detect failure of a coordinator that
never creates the marker. Thus lease handling must be connected explicitly by
the caller. Existing solvers were not touched during implementation or testing.

Default guards are a one-hour wall limit, 4,000 MiB **address space per child**,
256 MiB free-disk floor, and 100 million proof zero bytes/records. Limits are not
an aggregate machine-memory budget; choose worker counts and caps accordingly.
Canonical binary DRAT has one zero byte per record. The count guard conservatively
counts every zero byte and cannot be raised above 100 million for this default-
width checker. Hitting a limit yields no acceptance, even if work was substantial.

## Memory and CPU assessment

DSR `--forward` explicitly selects streaming parsing (`dsr-trim.c`, main option
dispatch). It does not load the whole proof before checking. Streaming witness
storage is bounded to the current witness, and `global_data.c` garbage-collects
deleted literals. **Its overall memory is not constant:** clause IDs, formula
entries, watches, hash tables, and other state remain. `commit_clause()` increments
`formula_size`; literal garbage collection does not imply reclamation of every
clause-ID slot. Default-width IDs/counters are signed `int`, so unlimited streams
also raise index-limit risks. The retained default-width binary is unchanged;
the earlier problematic LONGTYPE build is not used.

Full resource guards and direct-child cancellation were exercised. Fifteen
controls passed, including real Kissat SAT/UNSAT, malformed empty-clause rejection,
VALID-only rejection, UNKNOWN, wrong solver exit, early checker failure before
FIFO open, timeout escalation, abort-file/SIGTERM handling, supervisor SIGKILL,
record-count guard, binary-hash mismatch, and early verified-prefix draining.

An 8 MiB synthetic repeated-clause stream plus a valid UNSAT suffix was checked,
with exact byte count/hash and no proof retained. Its wall time, combined child
CPU, sampled RSS, and relay CPU are in `streaming-feasibility.json`. This is a
transport/duplicate-clause control, **not representative of RAT-heavy search**.
The tiny runs cannot establish a long-run memory bound or realistic solver
slowdown. Forward checking consumes additional CPU; when it falls behind, the
bounded relay intentionally throttles Kissat. Runtime RSS sampling may miss
short-lived peaks; aggregate child max-RSS includes pre-exec process overhead.

Using the owner's reported 50 MB/minute compressed rate and 16 GB free, retained
proofs would use that space in roughly `320 / workers` minutes. This runner removes
proof-file growth; CNF copies, logs, checker RAM, and CPU remain real costs. Any
future long-run experiment must monitor those quantities and preserve the final
online-check record. No real search worker or lease was started by this task.
