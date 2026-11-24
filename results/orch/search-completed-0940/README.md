# Completed focused searches

All files preserve complete solver stdout/stderr. No target circuit was found.

Dirty C6 with exactly nine gates returned UNSAT after29.69 process seconds. C6 with three private leaves at twelve gates reached the60-second cap without a verdict, as did the restricted four-AND variant. These use the reviewed general Search.py encoding with distinct backward binary fan-ins, all nonfinal gates used, positive firing/negative failure pruning, operand incomparability, topological symmetry ordering, graph automorphisms, and an existential dirty AND. The UNSAT result is scoped to that exact constrained model; it is not a lower bound excluding arbitrary smaller dirty circuits.

Alternative6 nearby repairs use the reviewed SearchNearby.py transformer and the unpruned unordered base28 encoding. Existing near-3-7 and near-3-10 seeds each returned UNSAT within six ordered-fan-in/operator edits. Multi-dirty-near-1 also returned UNSAT within six edits. Multi-dirty-near-2 at eight edits reached180seconds without a verdict. Seeds are INVALID and preserved in the sibling nearby-search and alternative6-run-004 packages. Each UNSAT result excludes only its stated bounded neighborhood.

Reproduce C6 CNF generation with Search.py `--case c6 --gates 9 --dirty --first-pair-orbits c6-automorphisms.json --output scratch.cnf`; use `--case c6private --gates 12` and the corresponding orbit file, optionally `--and-count 4`, for the other runs. Each solver uses `cadical -t 60 scratch.cnf`. Nearby metadata and sources are in the sibling nearby-search package; use edits6 or edits8 and the named seed.
