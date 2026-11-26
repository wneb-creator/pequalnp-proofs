# Signed full-Petersen cap-18 checkpoint and exact optimizations

This package freezes native research for L-meta-2373. The cap-18 search is
**still running**, with layers 1–7 complete and 222,594 states at depth 7.
It is not a Lean proof, a checker acceptance, or a claim that cap 18 is closed.
The separate cap-17 runs close in this native model; their exact comparison
receipts are included. Any candidate's explicit NOT cost requires a separate
check: the search gives complements freely and charges binary operations only.

The full current implementation is `signed-hash.cpp`. It includes the checked
restart loader, sampled-row projection shortcut, exact cached row-collision
predicate, compact paid projection banks, and exact hash-to-ID wire index.
Its SHA-256 is
`6b40580589a22854163d6d6b5144b920acad4d96543e0bd83b0b9c9441e4ad9b`.
Every hash bucket candidate is compared using all 1,024 truth bits. Hash
collisions cannot merge different signals; forcing every hash to zero is
covered by the supplied tests.

## Scope and completed checkpoints

The target is the Petersen edge function on ten raw Boolean inputs, with edges
`01,12,23,34,40,05,16,27,38,49,57,79,96,68,85`. Variable `i` is bit `i` of an
assignment index. The four normalized signed operations are AND, OR, AND-NOT,
and NOT-AND. Every live function is represented in its phase false at zero.
The search checks all 1,024 assignments for collision exclusions and uses
all 120 Petersen automorphisms for canonicalization.

| Completed depth | Retained states | Wire records | Implementation |
|---|---:|---:|---|
| 0 | 1 | 10 | child collision |
| 1 | 6 | 190 | child collision |
| 2 | 159 | 2,548 | child collision |
| 3 | 4,189 | 32,353 | child collision |
| 4 | 75,766 | 324,523 | child collision |
| 5 | 560,141 | 2,559,729 | child collision |
| 6 | 965,585 | 6,356,809 | sampled projection / restart |
| 7 | 222,594 | 9,483,628 | compact banks / cached collision |

The exact hash index resumed depth 7 and is exploring depth 8. Immediately
after loading the full checkpoint it used 2,076,216 KiB RSS; its loader peak
was 3,244,932 KiB. These are measurements on the execution machine, not memory
guarantees. Four CPU equivalents and a 16-GiB cgroup limit were available;
other Lean jobs ran concurrently, so wall times are not controlled benchmarks.

`checkpoint-manifest.json` contains source hashes, every completed frontier's
framing/counts/SHA-256, and the hash of its committed wire-table prefix. It
also verifies byte identity across all three restarts at depths 5, 6, and 7.
The large frontier and wire binaries remain local and are omitted here.
Wire files may contain records appended by partial work on the next layer;
only the first `144 * wireCount` bytes belong to a given checkpoint.

`logs/` contains each invocation's complete stdout and stderr through the
freeze. Previous invocations were deliberately stopped after completing a
checkpoint, so stderr can include partial next-layer progress. The current
worker's logs are a frozen prefix while it continues elsewhere. Reported
`sec` values are cumulative within that invocation, including restart work.

## Projection basis

`signed_data.py` reads L670's 106 signed columns, L6581's 215 signed columns,
and L6581's whole H9 signed bound 15, then embeds them in the ten vertex-false
cofactors. Deduplication gives 1,185 pools. The binary data SHA-256 is
`f350a4b13d7c05ec8fbf7ebe82e2c30d633a970875b69e2034378def61899e2c`.
The source-specific certificate payloads are not reinterpreted as one format;
the native engine uses each checked column's domain, available signals and
bound. The independent reconstruction audit is included under `evidence/prior`.

No monotone-only factor exclusion, monotone bound 16, or inferred signed
bound 17 is used. The separate L6581-only cap-17 run, which drops all 107 pools
whose selected witness needs L670, also closes; its complete logs are included.
That 5,230-state run is the source for a separate Lean replay effort. This
package makes no claim about that effort's completion.

## Validation and independent review

`evidence/hash`, `evidence/compact`, and `evidence/collision-cache` preserve
the prior frozen sources, complete test streams, comparison receipts and
attributed independent reviews. The complete final source is unchanged from
the reviewed hash version; it composes the already reviewed earlier changes.

* Every optimization reproduces all 18 cap-17 frontier files, the complete
  wire table and the collision histogram byte for byte.
* Compact-bank comparison expands 832,145 specifications over 1,001 sampled
  cap-18 parents and verifies identical metadata and ordered words.
* Cached collisions agree on 94,089 actual eligible children, 123,504 complete
  operation/retention comparisons and 17,920 synthetic comparisons, including
  shuffled wire order and forced stamp wrap. Exact first witness pairs agree.
* Both known 20-gate Petersen circuits survive all pruning checks, with all
  120 symmetry images checked on all 1,024 rows.
* Forced-zero-hash tests verify those known circuits plus 2,000 distinct
  words, repeated/absent lookup, vector growth and target-DAG emission.
  The emitted known circuit passes phase reconstruction on all assignments.
* Restart testing checks same-directory and symlink-alias rejection, short
  reads, duplicate live signals, causal prefixes, complete wire equations
  and byte identity after restart. Input is checked before use, and outputs
  are checked on close. The supplied framing script is a smaller auxiliary
  check; it does not replace the executable's semantic restart validation.

The hash source, compact-bank change, and restart change each have independent
source-review reports. The collision cache was independently reviewed by the
signed search owner; its author supplies the comparison and synthetic tests.
The reports distinguish source review from execution evidence. Native tests
and independent review are still distinct from Lean kernel verification.

## Reproduce

Use Python 3 and a C++20 compiler on a little-endian machine. No third-party
Python packages are needed. In this package directory, create fresh build
and run directories and generate the data:

```sh
python3 signed_data.py --repo /path/to/pequalnp-proofs --output /path/to/build
g++ -O3 -std=c++20 -I /path/to/build signed-hash.cpp -o /path/to/build/signed-hash
g++ -O3 -std=c++20 -DFORCE_WIRE_HASH_COLLISIONS -I /path/to/build hash-known-sanity.cpp -o /path/to/build/known-sanity
g++ -O3 -std=c++20 -I /path/to/build hash-collision-unit.cpp -o /path/to/build/hash-unit
```

Keep `cached-collision.hpp` beside the source. The quoted include searches
that source directory first; do not leave an unrelated generated
`probe-data.hpp` there. Assertions must remain enabled for the test harnesses.
`-march=native` is an optional machine-specific performance flag. Compile
output can contain a return warning for the renamed, unused engine entry
point in test harnesses; the actual program entry is ordinary C++ `main`.

Run from a fresh directory containing the generated `pools.bin`, preserving
both streams. The three positional arguments are maximum explored depth,
all-paid-prefix exploration enabled, and initial binary budget:

```sh
/path/to/build/signed-hash 17 1 17 > search.stdout 2> search.stderr
/path/to/build/signed-hash 18 1 18 > search.stdout 2> search.stderr
```

Use a separate output directory for each invocation. Restart adds the saved
run directory and saved depth, and rejects the same directory or aliases:

```sh
/path/to/build/signed-hash 18 1 18 /path/to/previous/run 7 > search.stdout 2> search.stderr
```

Run `known-sanity` and `hash-unit` in separate test directories containing the
same pool data. The latter writes `target.json` for a previously known
20-gate circuit; this is a format test, not a newly found counterexample.
`python3 phase_optimize.py target.json --output physical.json` reconstructs
an explicit AND/OR/NOT circuit and verifies every truth-table row.

`PRIOR-README.md` documents the model and trace formats in detail. In brief,
`wires.bin` contains 144-byte records (sixteen 64-bit words and four 32-bit
origin fields). A frontier starts with 64-bit wire and state counts, then
each state has 32-bit width/depth, live IDs, and operation/operand triples.
A target DAG uses input slots 0–9 and gate-output slots `10+j`; it is written
on exit status 4 and must be separately checked before interpreting its cost.

`SHA256SUMS` covers every frozen package file except itself.
