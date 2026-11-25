# Construction experiments for L-meta-2625

The desk assigned a reduction, not a proof submission. No 33-gate witness was found.

## Useful smaller geometry

Retain S = {0, 1, 2, 3, 4, 9, 10}, the union of lines 0 and 1. The residual has seven point inputs and thirteen line inputs, 28 incidence edges, and a standard 34-gate circuit. A hypothetical 33-gate separator, combined with the six omitted point stars (29 gates) and one final OR, would give the requested 63-gate circuit.

The residual graph consists of a subdivided K3,3, two line vertices adjacent to four point vertices each, and two line leaves at the common point. The generic negative rows permit eight additional pure point triples on the two retained lines, plus the concurrent line triples. Therefore a lower bound for the exact edge function does not immediately refute the smaller partial synthesis problem. Feasibility at 33 gates remains unknown.

## Checked baseline

Core34.lean proves the exact proposed core hypothesis with bound 34 in place of 33. It explicitly gives 34 binary AND/OR gates, output wire 53, verifies all 28 positive incidence pairs, and rejects all listed transformed generic negative inputs. The Lean compiler completed with exit code 0. Its full stdout and stderr are in core34-build.log, which is empty. This is a checked baseline only, not a proof of the required 33-gate hypothesis.

Command, from the repository lean directory:

    source /tmp/oec/pequalnp-pilot-50/toolchain/env.sh
    lake env lean /tmp/oec/pequalnp-pilot-50/construction/Core34.lean

A separate formula-based variant was stopped after the direct baseline finished, to free CPU for the completion proof. Core34Fast.lean is not claimed as checked.

## Searches

Two MILP searches tested a seven-input, seven-gate gadget for three collinear point stars. Both reached their 180-second limits without a witness or an infeasibility proof. The second search additionally required every essential input and every nonfinal gate to be used.

Four stochastic searches tested the 20-input residual. The first two fixed a 33-gate genotype; their best candidate missed one positive incidence pair. The third allowed inactive helper gates and temporarily larger circuits. The fourth started with a safe collinear cubic term added to the standard circuit. The latter two found no correct circuit smaller than 34 gates. These failed searches are not lower bounds and do not establish feasibility of the 33-gate hypothesis.

Complete programs and stdout/stderr logs are retained in this directory. Completed search statistics:

- core-search.log: {'done': True, 'best': 3, 'iters': 37629051, 'restarts': 1882, 'time': 240.00011361100002}
- core-search-weighted.log: {'done': True, 'best': 1, 'iters': 26611559, 'restarts': 134, 'time': 240.00018311400004}
- core-search-slack.log: {'done': True, 'best': 34, 'iters': 12641430, 'restarts': 26, 'time': 300.00008479099995}
- core-search-cubic.log: {'done': True, 'best': 34, 'iters': 13599247, 'restarts': 28, 'time': 300.000006913}

Recorded UTC: 2026-11-25T00:47:42.535253+00:00
