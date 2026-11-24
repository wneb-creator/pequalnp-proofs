# L-meta-1024 finite-search archive

Snapshot prepared 2026-11-24 03:26 UTC by counterexample_search for independent
review. This archive contains no proof of the posted theorem and no valid
counterexample to it. The actual Lean file is maintained by root.

## Verified scopes

| Experiment | Outcome | Scope |
|---|---|---|
| Symbolic three-output local synthesis | UNSAT in both projective triple orbits | Ten other outputs are restricted to their fifteen direct OR-tree shapes; eight residual gates. This is not an unrestricted lower bound. |
| Original full 38-gate query | UNKNOWN after 60 minutes | No model or UNSAT certificate. |
| Original normal-dual query | UNKNOWN after 30 minutes | Exact-line dual minterms assumed. |
| Three original low-fanout queries | UNKNOWN after 30 minutes each | No model or UNSAT certificate. |
| Symbolic five-output local query | UNKNOWN after 30 minutes | Eight fixed direct-tree outputs and fourteen residual gates for outputs 2,3,6,8,9. |
| Five strengthened queries | Externally interrupted around 03:18:50 | All solver processes were zombies; gzip proof streams are incomplete and retained in scratch. |
| Five detached restarts | Running as of this snapshot | Fresh 90-minute budgets began 03:21:40–03:22:29. See launch manifest. |

Every proposed gap counterexample is checked on all 3,003 original required
input rows by an independent scalar evaluator after bitset validation. No
candidate has passed that check.

## Auxiliary counterexample

`generic/majority-three-triples-counterexample.json` refutes only the auxiliary
conjecture `gates >= 2*d-c-1`, where d is minimum satisfying support and c is the
number of mandatory variables. Form three disjoint AND3 blocks A,B,C, then
compute `(A AND B) OR (C AND (A OR B))`. This uses ten gates, has minimum
satisfying support six, and has no mandatory variable. The conjectured bound is
eleven. All 512 assignments were checked independently; exactly 22 satisfy it.

The five smaller dense SAT diagnostics in `generic/` were UNSAT. Their complete
CNFs and logs are included, along with four small completed compressed LRAT
traces. The fifth 5.3 MB completed trace remains at the path recorded in the
manifest. These finite diagnostics do not establish the false generic theorem.

## Other diagnostic candidates

`diagnostics/explicit29-diagnostic.json` is valid only on the 157 dual inputs
contained in a single projective line. It fails the required band and is not a
gap counterexample. `diagnostics/repair-best-approximation.json` is a 38-gate
heuristic approximation with eight correct outputs and 64 errors in each of five
outputs. It also is not a gap counterexample.

## Encoding, normalization, and replay

`records/normalization-notes.txt` records the exact mathematical assumptions,
their independent review, and which restrictions are backed by Lean lemmas.
The five live restarts use at least four globally nonordinary outputs and at
least eight syntactic input dependencies for each such output. They also use
exact support, live internal gates, output sinks, lexicographic internal-gate
order, and at least two AND gates (two OR gates in the dual search).

The full query constrains all 3,003 original band rows. The normal-dual query
constrains all 1,716 six-point dual rows and the thirteen exact lines, with AND
output roots. Each query adds 104 independently reviewed partial off-band rows.
The three fanout queries start from 671 band rows and cover the three audited
first-pair cases after selecting an input of fanout at most three.

The sources are verbatim exploratory files, retaining their original absolute
scratch paths and the bundled CaDiCaL path. They are not a portable installer.
To replay elsewhere, relocate the shared scratch prefix consistently in all
source files and point `cegis.py`'s SOLVER constant at a compatible CaDiCaL.
The resume sources import the other archived Python sources. The archived
permutation tables contain the explicitly checked finite symmetry witnesses.

The running jobs are detached Python monitors with complete file logging, PID
records, nice 15, a 90-minute wall budget, and a 6.5 GiB free-disk floor. Resource
decisions must use `/sys/fs/cgroup/memory.current` and `memory.max`, not host
MemAvailable. Root alone owns the desk lease and publication.

`manifest.json` hashes every copied source and complete historical diagnostic
file. Large current CNFs, ongoing solver logs, and incomplete LRAT streams remain
in scratch and are referenced by the launch/interruption records. A solver
UNSAT result and an LRAT trace do not by themselves prove the posted Lean theorem:
the circuit normalization, CNF translation, and kernel certificate reconstruction
would all require formal checking.

This directory is branch metadata. It must be excluded from any eventual proof
PR, whose diff must contain the single required Lean proof file.
