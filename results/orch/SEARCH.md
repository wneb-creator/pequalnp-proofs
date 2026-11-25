# L-meta-2592 circuit-search record

This records computational searches for the leased Petersen graph problem. No
counterexample to the posted statement has been found. A SAT timeout is not an
UNSAT result, and the searches below are not a Lean proof of the posted statement.

## Encodings and validation

The graph has 10 vertices and 15 edges. Its edge function is false on exactly 76
of the 1024 input assignments. Its independence number is 4, and it has 5 minimum
vertex covers, each of size 6.

`search_sat.py` implements a one-hot circuit encoding with shared gate-operation
and fan-in selectors. Wire values are separately constrained for each sampled
input. Every returned model is evaluated independently on every input before it
can be reported as a witness. The encoding was tested with the known 20-gate
circuit from `L_meta_1755.lean`, fixed gate by gate, on all 1024 inputs; CaDiCaL
returned SAT and direct evaluation matched the graph function.

The generic search restricts circuits to ordinary useful gates, distinct binary
operands, topologically earlier fan-ins, and a final-gate output. It does not
establish a completeness theorem for that normalization. Optional colexicographic
fanin ordering is a search restriction, also without a formal completeness proof.

Free-negation searches use signed binary gates. Every internal wire can be
complemented, with downstream signs adjusted, to make it false on the all-zero
input. The normalized operations are AND, OR, AND-NOT, and NOT-AND. This removes
the otherwise redundant phase choice at each internal wire. The normalized SAT
encoding implements this by forbidding the other four essential signed binary
truth functions.

The primary-retention restriction for paid-NOT circuits is based on the team's
separate sole-reader argument. A binary gate on two primary inputs forces each
of those inputs to have another semantic reader. NOT's ignored second operand
does not count as a reader. For signed circuits the restriction is applied only
to the first gate.

## Completed general searches

| Search | Budget | Result |
| --- | --- | --- |
| 19 gates, one NOT, first gate OR(0,1), CaDiCaL | 180 seconds | Unknown / timeout |
| 18 signed binary gates, CaDiCaL | 180 seconds | Unknown / timeout |
| 18 signed binary gates, Kissat | 300 seconds | Unknown / timeout |
| Petersen minus vertex 9, 16 gates, one NOT | 180 seconds | Unknown / timeout |
| Repair the best approximate 19-gate circuit, change at most 3 gates | 120-second cap | UNSAT in the stated repair domain |
| Same repair, change at most 4 gates | 180 seconds | Unknown / timeout |
| Repair the best approximate signed-18 circuit, at most 4 changes | 180 seconds | Unknown / timeout |
| Signed-18, zero-preserving phases and colex fan-ins | 300 seconds | Unknown / timeout |

The first core sample set has 91 inputs: all 76 independent sets and the 15 edge
pairs. Later searches use 237 rows by also including every triple and every input
of Hamming weight at least 8. This includes the all-one endpoint.

The C++ local search completed 641.4 million 19-gate mutations and approximately
315.6 million signed-18 mutations. Neither produced an exact circuit. Their best
saved candidates each disagree with the target on 9 inputs; these are not
counterexamples or checked results.

## Restricted star-cover synthesis

A minimum vertex cover yields six OR-neighborhood outputs, followed by six
center AND gates and five final OR gates. Computing those six OR outputs with
8 gates, including a NOT, would give a 19-gate counterexample. Each cover has
three internal edges, so there are eight orientations to test per cover.

For the cover `[0,1,3,7,8,9]`, all eight orientation encodings returned UNSAT for
8 normalized gates and six selectable outputs. The 112 sampled rows already
sufficed. The multioutput encoding was separately validated with a fixed
8-gate pair-OR family containing two NOT gates; that instance returned SAT.

An exact automorphism enumeration found 120 Petersen automorphisms. They act
transitively on the five minimum vertex covers. The orientation-0 family's orbit
has size 20, so not all forty cover/orientation formulations belong to one orbit.
Testing all eight orientations of one cover nevertheless covers all forty by
cover transitivity.

## Smaller finite closure computation

`search_star_closure.py` uses only 12 test inputs: all-zero, the ten singleton
inputs, and all-one. A wire is represented by its 12-bit truth mask. The initial
available masks are zero and `2048 + 2^(i+1)` for the ten input wires. Gate
operations are bitwise intersection, union, and complement within 4095.

For a fixed orientation there are six distinct target masks, none of which is
initially available. An eight-gate solution therefore has at most two gates
whose masks are not among those targets. The computation greedily closes all
target masks obtainable from the available masks, then enumerates up to two
additional auxiliary masks, closing targets after each addition.

All eight orientation computations returned false. The frontier sizes were
`[1,79,3901]` for orientations 0, 3, 5, and 6, and `[1,78,3818]` for
orientations 1, 2, 4, and 7. The separate elimination agent is checking this
finite condition in Lean. The general completeness argument relating arbitrary
circuits to the closure computation is not yet formalized here.

Complete solver and compiler output is retained under
`/tmp/oec/pequalnp-pilot-117/search/`. Search sources are under
`results/orch/lemmas/`. Only the root agent owns the desk lease and submits work.

## Lease interruption

At 2026-11-25T14:42:47.847408+00:00, root reported HTTP410 on the lease renewal and requested all work stop. The active paid19/exactly-one-NOT SAT run was terminated with SIGTERM; the subprocess returned -15 (SIGTERM), with no solver verdict and no witness. ABC compilation remains paused. No further searches or builds were started. Complete generated solver logs and models were copied into `results/orch/search-artifacts/`; CNFs are gzip-compressed without loss, with uncompressed SHA256 hashes in `MANIFEST.json`.

At 2026-11-25T14:47:23.424691+00:00, the root requested final cleanup after the shared-lease retry. All five paused ABC build processes were verified by working directory and executable name, then terminated; the build exited143. No active search backends remain, and all search-driver sessions have ended. Final diagnostics are `search-artifacts/cleanup.json` and `search-artifacts/abc-build-final.log`.
