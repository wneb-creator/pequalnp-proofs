# Fano searches for L-meta-2583

These are exploratory programs and complete diagnostic logs, not Lean proofs or
lower-bound certificates. No 26-gate witness has been found. The stochastic
counts below count mutation attempts, including repeats, not distinct circuits.

## Exact finite test set

Inputs 0 through 6 are points; inputs 7 through 13 are lines. Point p is incident
to line l when p equals l, l+1, or l+3 modulo 7. `constraints.txt` lists 58
assignments as 14-bit integers, in this order:

- The 21 incident pairs, ordered first by line and then by point.
- All 37 maximal independent sets of the incidence graph, in increasing bitmask
  order: 21 have size 4, 14 have size 5, and two have size 7.

For a monotone circuit, agreeing with the incidence function on these assignments
implies agreement on all 16384 assignments. Every true input contains an incident
pair; every false input is contained in a maximal independent set.

The structural_proof agent independently regenerated and checked this entire
set, including its order. It also independently audited the C++ full-circuit
search, its cached suffix evaluation, and its explicit full truth-table witness
check.

## Full-circuit local searches

`fano_search.cpp` and `fano_search_low.cpp` search 26-gate AND/OR circuits with
earlier-wire operands. They start by deleting and redirecting one gate of a
27-gate star circuit, then mutate gates. Their objective is the number of wrong
decisive tests. The low-temperature variant mostly accepts only improvements
and ties.

- `search.log`: 601 seconds, 4,330,000,000 mutation attempts, best distance 1.
- `search-low.log`: 601 seconds, 5,610,000,000 mutation attempts, best distance 1.

Neither run found a circuit agreeing with all 58 tests. `best26.txt` and
`best26-low.txt` are failed candidates, not counterexamples. A purported success
would also be checked against all 16384 input assignments before returning a
successful program status.

## Small-block searches

`fano_block.cpp` searches a k-gate block whose function is below the Fano
incidence function. Let M be the set of incident pairs it accepts and let tau be
the minimum vertex-cover size of the remaining edges. Completing the remaining
edges by stars and joining the results costs at most

    k + 21 - |M| + tau.

Therefore a block with `k - |M| + tau <= 5` yields a circuit of at most 26 gates.
The program precomputes tau for all 21-bit M by enumerating all vertex subsets
and applying a subset-minimum transform. The structural_proof agent independently
audited this table, the objective, the edge order, and seed rewiring.

The tested sizes are 6, 10, 14, 18, 22, and 26, each one gate less than a circuit
for a union of complete line stars. Known baselines of s complete stars have
4s-1 gates, accept 3s edges, and leave a cover of size 7-s, giving score 6. All
seven baselines were independently recomputed in Python.

The original block search charges 128 per false-positive test. The
`fano_block_soft.cpp` variant charges 2 to permit temporary false positives.
Both require zero false-positive tests before reporting any candidate.

## Exact synthesis encodings

`fano_smt.py` encodes bounded wire selectors and 58-bit wire signatures in Z3.
`fano_onehot.py` uses one-hot Boolean selectors and explicit Boolean gate values
instead. Both use the system `libz3.so.4` through ctypes; no external package or
credential is required. Both constrain operands to be distinct and ordered,
every non-output gate to have a later reader, and each gate to differ from each
of its operands on the decisive tests. They search exactly the stated gate count.

The anchored BV run additionally fixes the first gate to OR(0,1) and applies an
adjacent-independent-gate ordering restriction. This is a targeted search, not
an audited exhaustive symmetry quotient.

- General BV26: UNKNOWN under a configured 180-second budget.
- Anchored BV26: UNKNOWN under a configured 300-second budget.
- Fixed canonical BV27: SAT, validating the encoder against a known circuit.
- Fixed canonical one-hot27: SAT, 1.338 seconds.
- General one-hot26: UNKNOWN, reason `canceled`, 301.024 seconds under a
  300-second budget.
- General one-hot27: UNKNOWN, reason `canceled`, 121.624 seconds under a
  120-second budget. This solver setup did not rediscover the known upper bound
  quickly.

The direct-clause encoder `fano_cnf.py` avoids mux Tseitin variables and disables
SAT variable elimination. Underlying variable polarities put the canonical
star circuit at the all-false initial phase. These are search hints, not fixed
gate assertions or restrictions on the represented circuits. It first checks
that the phase seed violates zero clauses for 27 gates and exactly one clause
for the 26-gate seed. The unrestricted27 run was SAT in 3.177 seconds. Its model
was independently parsed and checked against all 16384 assignments; see
`cnf27-validation.txt`. A 30-minute unrestricted26 run started after the root
renewed the lease at 15:02:27 UTC on 2026-11-25. It was terminated by SIGTERM
at 15:06:24 UTC after the root reported desk HTTP410. It produced no verdict.
This is an external termination, not a solver result or proof of impossibility.

The structural_proof agent independently audited `fano_cnf.py`: ordered
one-hot selectors, selected-wire equalities, the six conditional AND/OR clauses,
later-reader constraints, all 58 output units, polarity renaming, and seed
deletion/rewiring all passed the static review. A SAT result still requires
independent model validation and then a Lean proof. An UNSAT result from Z3
would not itself be a Lean result.

The first two logs came from an earlier wrapper that requested a model after
UNKNOWN, causing a model-unavailable error. Their specific reason for UNKNOWN
was not captured; timeout is inferred, not established by the log. The current
wrapper requests `reason-unknown` and does not request a model after UNKNOWN.
UNKNOWN is not UNSAT and supplies no lower bound.

Replayable generated SMT-LIB files are retained for the completed runs. The
Python programs currently refer to the original scratch directory
`/tmp/oec/pequalnp-pilot-138/semantic`; to regenerate inputs elsewhere, change
their `root` path or place these files at that path. C++ programs take their
constraint and result paths as arguments.

All searches stopped at 15:06:24 UTC on 2026-11-25 after the root reported
desk HTTP410. See `termination-status.txt`. The soft-block search was also
terminated with exit143 and had found no candidate. Its complete output is
`search-block-soft.log`. The hard-block search had completed600 seconds and
4,130,000,000 mutation attempts, with best score7 for all six sizes.

`fano_block_baseline.cpp` was prepared and compiled but never run. It starts
from exact star baselines at sizes3,7,11,15,19,23 (initial objective6), and
permits two simultaneous gate mutations. The hard/soft block programs actually
run used sizes6,10,14,18,22,26.

The one-hot mux encoder with phase hints also returned UNKNOWN, reason
`canceled`, after120.503 seconds; its completed output is `onehot27-phase.log`.
Only the direct-clause CNF encoder found the unrestricted27 positive control.
No search found a26-gate witness. No UNSAT verdict was obtained.
