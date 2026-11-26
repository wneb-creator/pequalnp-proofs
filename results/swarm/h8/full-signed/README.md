# Full Petersen signed contraction experiment

This is reproducible native research for gap L-meta-2373. It is not a Lean proof
of the gap, nor a kernel-checked signed lower bound. The engine searches a
normalized signed binary contraction model: AND, OR, AND-NOT, and NOT-AND each
cost one binary operation, and complement availability is free. An explicit
NOT count must be established separately for any candidate circuit.

The target is the 10-variable Petersen edge function with edges
`01,12,23,34,40,05,16,27,38,49,57,79,96,68,85`.
Variable `i` is bit `i` of row indices 0 through 1023.

## Checked runs

* `cap16.stdout`: the original engine closes cap 16. There are 720 root moves,
  675 projection exclusions, and 45 remaining OR-consume moves. These reduce
  to two symmetry classes, each rejected by an exact row collision.
* `first-step-audit.json`: an independent scalar replay excludes all 720 moves
  directly, using only the ten whole H9 signed lower bounds 15. It has 675
  projection witnesses and 45 collision witnesses. It does not use the 321
  smaller column bounds.
* `cap17.stdout`: the original engine closes cap 17 in 37.4 seconds on the
  execution machine, with the last frontier emptied at level 10.
* `child17.stdout`: moving the exact collision check before canonicalization
  also closes cap 17. Its frontier widths, including the root, are
  `1,2,24,265,1634,2594,594,46,2,0`. There are 5,162 nonempty retained states.
  This run took 48.1 seconds; timings depend on machine load.
* `fast17.stdout`: the sample-row optimization closes the same case in 16.0
  seconds. Every frontier and the complete wire trace are byte-identical to
  `child17`. `performance-byte-identity.json` records this check.
* `no670-cap17.stdout`: removing all 107 pools whose selected witness needs
  L670 still closes cap 17. Its frontier widths are
  `1,2,24,265,1634,2621,634,47,2,0`, totaling 5,230 nonempty states. Only L6581
  signed column bounds and its whole H9 bound are used in this run.
* `sanity.stdout`: two known monotone 20-operation Petersen circuits survive
  every signed projection exclusion, and their wire DAG images agree with
  scalar row permutations for all 120 automorphisms and all 1024 rows.
* `signed-known-sanity.stdout`, when present, is the separate reviewer's run
  that also checks the exact row-collision rule on the known circuits.
* `phase-known20-result.json`: phase optimization preserves the known
  20-operation circuit, requires zero NOT gates, and matches the target on
  all 1024 rows. `phase-simple-result.json` checks a small signed example; its
  nonempty `petersen_errors` list is expected because it is not a Petersen
  circuit.

All stdout and stderr files for these runs are preserved in full. An empty
stderr file means no diagnostics were printed. The separate cap-18 experiment
was still running when this package was frozen; it is not claimed closed here.

## Projection basis

`signed_data.py` reads existing Lean sources from the supplied repository:

* `L_meta_670.sgC`: 106 signed column tuples.
* `L_meta_6581.rootSCols`: 215 signed column tuples.
* `L_meta_6581.nineFloor`: the whole H9 signed lower bound 15.

The two source graphs and their nine raw inputs agree. Each column is embedded
in each of the ten vertex-false cofactors by a graph automorphism. Its raw
signal bank includes constants and complements. An augmented-input code in
the high bits of an L670 `z` field is decoded into that additional signal and
its complement. All L6581 `z` fields are below 512. The `q,s` certificate
payloads are not decoded by the native engine: their encodings differ between
the two source files, while the already checked column conclusion gives the
same domain/raw-bank/lower-bound meaning used here.

Identical domain-and-bank pairs retain their maximum bound, yielding 1,185
pools. The generated `pools.bin` SHA-256 is
`f350a4b13d7c05ec8fbf7ebe82e2c30d633a970875b69e2034378def61899e2c`.
`signed-binary-pool-audit.json` records an independent scalar reconstruction
of all pools and their exact byte match. No monotone bound 16, monotone Horn
factor cut, or previously inferred signed bound 17 is used.

`L6581-cofactor-rowmaps.json` supplies independently checked cofactor row maps,
the source's Extended pin coordinates, and essential-input row pairs. Its
Extended pin order is `[9,7,5,8,6,4,2,0,3,1]`; do not confuse those coordinates
with the native engine's standard variable-bit order. The two swap-witness
files give the 45 OR-consume collisions in each coordinate system.

`native-pool-map.json` maps each native pool ID to one checked source witness.
Its record schema is `(vertex, sourceCode, sourceIndex, bound, zeroMask,
oneMask)`, with source indices zero-based. Source 0 is L670 `sgC`, source 1 is
L6581 `rootSCols`, and source 2 is the whole signed H9 bound. Among equally
strong witnesses the map prefers L6581. There are 107 L670 witnesses, 1,068
L6581 column witnesses, and ten whole-cofactor witnesses.
`native-extended-row-permutation.json` gives both coordinate permutations on
all 1024 rows. `map_pools.py` reconstructs these files, checks every pool's
domain, root bank and bound against the generated binary, and checks all ten
isomorphisms against the independently prepared cofactor map.

## Reproduce

Use Python 3 and a C++20 compiler on a little-endian machine. No external Python
packages are required. First generate data in a new build directory:

```sh
python3 signed_data.py --repo /path/to/pequalnp-proofs --output /path/to/build
g++ -O3 -std=c++20 -I /path/to/build signed.cpp -o /path/to/build/signed
g++ -O3 -std=c++20 -I /path/to/build signed-child.cpp -o /path/to/build/signed-child
g++ -O3 -std=c++20 -I /path/to/build known-sanity.cpp -o /path/to/build/known-sanity
g++ -O3 -std=c++20 -I /path/to/build signed-fast.cpp -o /path/to/build/signed-fast
g++ -O3 -std=c++20 -I /path/to/build signed-resume.cpp -o /path/to/build/signed-resume
```

Run each command in a separate directory containing the generated `pools.bin`;
the executable reads it from its working directory. Save both output streams:

```sh
/path/to/build/signed 16 1 16 > search.stdout 2> search.stderr
/path/to/build/signed 17 1 17 > search.stdout 2> search.stderr
/path/to/build/signed-child 17 1 17 > search.stdout 2> search.stderr
/path/to/build/known-sanity > sanity.stdout 2> sanity.stderr
```

The positional arguments are maximum explored depth, whether to consider all
paid prefix steps, and initial binary budget. The published runs use paid
prefix exploration enabled. Do not use an explored depth beyond the budget.
The optimized collision table supports at most 20 live wires.

`signed-fast.cpp` uses a few actual rows from each pool domain to establish
that some live wires are nonconstant. The resulting upper bound on constant
wire count lets it skip pools whose bounds cannot exclude a child, before
forming the full restricted words. This does not assume monotonicity.

`signed-resume.cpp` adds checked restart support. From a different output
directory containing `pools.bin`, use:

```sh
/path/to/build/signed-resume 17 1 17 /path/to/old/run 5 > search.stdout 2> search.stderr
```

The last argument is the saved depth. Restart checks every input record and
wire equation, global signature uniqueness, causal prefixes, and distinct
available live wires. It rejects a source directory equal to the output
directory, including symlink aliases, before opening output traces. Restart
at depth 5 reproduces every remaining cap-17 frontier and the complete wire
trace byte for byte. No general proof of the restart implementation is claimed.

To reproduce the L6581-only run, first filter the generated data, then compile
`signed-fast.cpp` against the filtered header and run with the filtered binary
pool file in its working directory:

```sh
python3 filter_supported.py --input /path/to/build --map native-pool-map.json --output /path/to/filtered
g++ -O3 -std=c++20 -I /path/to/filtered signed-fast.cpp -o /path/to/filtered/signed-fast
```

`no670-old-pool-ids.json` maps each of the 1,078 filtered pool IDs to its original
1,185-pool ID. This deliberately drops 107 valid L670 bounds so that a later
Lean replay can use a single source certificate vocabulary.

The independent first-step scalar audit is rerun with:

```sh
python3 audit_first_step.py --reference first-step-audit.json --output replay.json
```

It checks every saved record, not merely aggregate counts.

## Search and trace formats

Each state contains a set of distinct normalized nonconstant live signatures
and one actual prefix producing them from ten raw inputs. A step selects two
different live signatures, one of four operations, and independently keeps or
consumes each operand. Normalization represents each nonconstant Boolean
function by the phase false at the all-zero row. Operation codes are:

| Code | Operation |
|---|---|
| 0 | `a AND b` |
| 1 | `a OR b` |
| 2 | `a AND NOT b` |
| 3 | `NOT a AND b` |

The engine uses live-width, signed XOR coverage, duplicate/constant output,
signed projection, and full 1024-row collision exclusions. It canonicalizes
the live set under 120 Petersen automorphisms but retains the original state
and its actual prefix. All paid-prefix banks come from actual causally
available prefix operations, each charged once; complements are added freely.
The known-state and monotone-factor mechanisms are inactive.

Generated traces are deliberately omitted from this source package because
they are much larger than the reproducible inputs. Their format is native
little-endian, with the following fixed-width fields:

* `wires.bin`: 144 bytes per record. The first 128 bytes are 16 `uint64` truth
  words, least significant row first. Four `int32` fields follow:
  `(operation, leftID, rightID, rawVariable)`. Record index is the global wire
  ID. Inputs have IDs 0 through 9. A negative field means absent information.
* `frontier-N.bin`: header `(uint64 wireCount, uint64 stateCount)`. Each state
  has `(uint32 liveWidth, uint32 prefixLength)`, then `liveWidth` `int32` wire
  IDs, then `prefixLength` triples `(int32 op, int32 leftID, int32 rightID)`.
  Remaining budget is `initialBudget-N`.
* `factor-states.bin` is empty; no factor cuts are active.
* `signed-collision-pairs.txt` lists positive row, negative row, and aggregate
  occurrence count for full row-collision exclusions.

These frontier traces retain complete states and prefixes but do not retain
individual move reasons, selected paid-prefix masks, or canonical permutation
witnesses. A separate certificate emitter must record or reconstruct those
before a Lean replay can be claimed.

## Candidate DAG and phases

A generated target exits with status 4 and writes `target.json`:

```json
{"inputs":10,"gate_count":2,"gates":[[0,0,1],[1,10,2]],"output":11}
```

This example is only a format illustration. Raw input slots are 0 through 9;
gate `j` produces slot `10+j`, and both operand indices refer to earlier slots.
The four operation codes are as above. Unlike global trace IDs, these are
ordinary causal DAG slot numbers. A target candidate must be checked on all
1024 rows before it is used.

```sh
python3 phase_optimize.py target.json --output actual-circuit.json
```

The phase optimizer exhaustively minimizes the number of explicit NOT gates
for that fixed signed DAG, with shared opposite-phase signals reusable across
consumers. It writes an AND/OR/NOT circuit and checks equality with the signed
DAG on every row. It also reports every Petersen target mismatch. The optimum
is specific to that DAG, includes its retained dead gates, and does not prove
global circuit optimality.

Independent review checked the pool transport, signed operations, paid-bank
construction, canonicalization, collision rule, child-check optimization, and
phase optimizer algebra. Those reviews and native runs remain distinct from
Lean kernel checking. `SHA256SUMS` records the frozen package files.


## Cap-18 performance checkpoint

`cap18-delivery/` freezes the reviewed current implementation, exact collision cache,
compact projection banks and full-equality hash index, with reproduction
commands and complete checkpoint receipts through depth 7. The search is
still ongoing at this snapshot: 222,594 states remain at depth 7. This is
native research, not a closed cap-18 search or a Lean lower bound. The package
records post-restart memory use and the earlier paired cap-17 optimization tests.
The final package review is in `cap18-package-review.json`; it distinguishes
independently checked frontier hashes from the owner's wire-prefix hashes.


The follow-up `cap18-result/` records completion: the native budget-18 signed
search exhausted its frontier first at depth 11, with no target found. It
retained 1,837,200 states, enumerated 2,126,363,024 moves and created
10,087,412 wire records. Complete logs and all 19 frontier hashes are included.
`cap18-completion-review.json` independently verifies those records and the
committed final wire prefixes. This remains native computational evidence,
not a Lean proof of a 19-binary-gate lower bound or the posted gap.
