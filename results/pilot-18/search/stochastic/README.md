# Candidate-only stochastic circuit optimization

This is a bounded heuristic for finding any circuit of at most 21 binary AND/OR
gates computing the eleven-input target. It does not constrain first junk,
second junk, prefix cleanliness, liveness, or any assigned shard. UNKNOWN and
ABORTED do not establish a lower bound or exhaustion.

`circuit_anneal.cpp` is a standalone C++17 engine. Its 40-bit truth vectors have
the sixteen edge inputs first and the twenty-four maximal independent inputs
second. It independently regenerates these rows from the fixed graph. Every
seed is scalar-checked on all 2048 inputs before use. The search deletes one gate
from a 22-gate seed, aliases its fanout to an operand or earlier wire, renumbers
references, and mutates operations, fanins, and the output selector. Constants
FALSE11 and TRUE12 are available; output gate wires start at 13.

The primary objective is `weight * false_negatives + false_positives`, default
weight four. A 0.02-per-live-gate tie-breaker is always smaller than one error.
Annealing cools during each restart interval; most restarts delete a gate from
a fresh baseline, while one quarter perturb the best circuit. The engine favors
mutations of live gates but also mutates dead gates. No effectiveness or
iterations-per-second claim has been established by the controls.

Every strict best improvement, including the initial circuit, is written to
`engine-result.json.best-N.json`. These are labeled partial, not witnesses.
The final result always preserves the best circuit. An exact boundary match
triggers a separate scalar 2048-input check inside C++ and stops the search.
Only a candidate path is printed for that event; circuit JSON is kept in files.

`stochastic_tools.py run` creates a fresh output directory, captures full engine
stdout/stderr, limits address space to 256 MiB, and enforces an outer timeout five
seconds beyond the engine limit. SIGTERM/SIGINT or the configured abort sentinel
stop the process group, escalating after two seconds. The child also handles
SIGTERM/SIGINT and checks its own wall limit every 1024 iterations. Uncatchable
supervisor death cannot run cleanup, but the engine retains its own wall limit.

On engine exit 10 plus its exact candidate status, the wrapper runs the separately
authored, hash-pinned `validate_raw_candidate.py`. This validates strict wire
structure, all 2048 original inputs, virtual-constant/alias/dead-gate elimination,
and all 2048 normalized inputs. Only exit zero and the expected hash-bound
`EXACT_AT_MOST_21` report produce `VALIDATED_CANDIDATE_REQUIRES_LEAN`.
The validation stdout/stderr and normalized report are retained. Lean proof is
still required. A wrapper exit zero alone is not a witness verdict: inspect
`result.json`.

The default abort path is the existing coordinator sentinel; only its existence
is tested. No desk requests, credentials, repository edits, or worker management
outside this wrapper's own child occur.

After independent review, a short first run can use a fresh directory:

```sh
python3 -B /tmp/oec/pequalnp-pilot-18/lean-setup/stochastic/stochastic_tools.py run \
  --engine /tmp/oec/pequalnp-pilot-18/lean-setup/stochastic/circuit_anneal \
  --pack /tmp/oec/pequalnp-pilot-18/lean-setup/stochastic/seed-pack-ready/seeds.txt \
  --output /tmp/oec/pequalnp-pilot-18/stochastic-candidate-134218 \
  --seed 134218 --seconds 60 --iterations 100000000 --restart 100000 --weight 4
```

The run directory retains full engine and validator logs, all best circuits, a
command/hash record, and a final status record. The wrapper's own stdout/stderr
should also be captured by the coordinating launcher. Repeated seeds follow the
same mutation trajectory with the same binary and pack; a wall-time cutoff can
stop at a different iteration. An iteration cutoff makes this stopping point
reproducible. Alternate weights such as eight are heuristic variants, not proven
improvements.

Controls include all 144 known-22 baselines, every possible deletion with five
aliases (15,840 circuits), scalar versus vector evaluation, independent deletion
renumbering semantics, and 15,840 random mutation checks. Wrapper controls use
fake completed engines and real raw-validator subprocesses: UNKNOWN, ABORTED,
unexpected exits, mismatched status, oversized/incorrect candidates, and a
preexisting abort sentinel. No stochastic search portfolio was launched during
these controls. There is no known exact 21-gate positive end-to-end fixture.

The fresh seed pack is prepared from the 144-case family with seed 134218.
Its manifest binds every original baseline hash and the pack bytes. Build and
control output is retained beside the source; `stochastic-review.json` records
the final hashes and verdict.
