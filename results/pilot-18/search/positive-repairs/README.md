# Positive-source candidate repairs: two UNKNOWN pilots

Both completed K3 pilots returned UNKNOWN after20seconds each. Neither produced
a SAT witness, an UNSAT result, or an exhaustion claim. The two additional local
five-gate formulas were generated but were not run in this pilot.

The two21gate sources independently compute exactly `F_G OR x9` on all2048
inputs. They accept every positive input and incorrectly accept22 independent
inputs, represented by five false-positive maximal-independent rows. Both
archived sources have a junk AND at gate14. One source has21live gates and the
other20. These are incomplete sources, not exact witnesses.

The generator reuses hash-pinned prior encoders. It retains the entire exact-target
boundary constraint set and frees the output selector. K3 counts changed gate
descriptions; local5 fixes every gate outside five heuristic holes. Neither mode
assumes a clean prefix, first-junk location, two junk gates, or liveness. The
source/controller reviews and full completed run logs are included.

`full-results.json` embeds every completed pilot directory file with its SHA256,
including all four solver stdout/stderr logs, portfolio and worker-limit record.
The outer controller stdout/stderr are separate complete files. The joint launch
record also mentions the coordinator's separate dirty22 annealer; it is retained
as launch provenance, not as a result of this package. Synthetic known22 models
in `controls-full-results.json` test the validator and explicitly exceed21gates.

No raw CNF is included. `reconstruction.json` binds all generation dependencies,
both exact source JSONs, and every expected generated file hash. Reconstruct:

```sh
python3 results/pilot-18/search/positive-repairs/reconstruct.py \
  /tmp/oec/pequalnp-pilot-18/positive-reconstruction-fresh
```

This stages only missing pinned files into the original named scratch hierarchy;
an existing different file causes rejection, never overwrite. It then regenerates
four CNFs into a fresh output directory, checks all14 generated file hashes, and
retains full generator logs. It invokes no solver, build, lease or network tool.
The original absolute scratch layout is needed because the reviewed dependencies
use those paths; their source bytes are preserved unchanged.

Historical preparation/handoff documents precede the completed pilot and are
preserved verbatim. This README and the complete final portfolio supersede their
READY or proposed-launch status. No exact21 Lean theorem or posted acceptance is
claimed. Main independent review of this preservation package remains required.
