# Stochastic search snapshot

These programs search for a smaller monotone circuit for the 21-input incidence function of K6. This package contains no proof and no circuit of size at most34. A valid35-gate baseline is included. Failure to find a witness has no lower-bound meaning.

The plain model contains seven/eight AND nodes. Each operand is an OR of selected primary inputs and earlier AND outputs; output is an OR of selected ANDs. It has no shared OR subexpressions. The shared model additionally has one/two linear OR helpers before the AND nodes. Both prune unreachable nodes when counting or decoding. Every source set and output set is nonempty. All physical gates are binary AND/OR and reference preceding wires.

Evaluation uses88 extremal cases:30 edge-pair positive inputs and58 distinct closed maximal-negative inputs. Every improved valid genome is independently decoded and checked on30 positive plus64 raw negative cases. These suffice for the monotone function: every positive assignment contains an edge pair, and each negative assignment extends to the raw negative case for its selected point subset. A prospective34-gate witness still requires Lean verification before being accepted as a refutation.

The objective combines gate cost and wrong-test counts, with randomized annealing and restarts. Seeds, elapsed wall time, mutation counts, and best valid costs are logged. The shared variant starts from35-gate stars or exact37/39-gate dirty-helper constructions, and maintains at most10000 low-error semantic states. All searches use one Python process and no external solver, network, environment credentials, or subprocesses.

The one-second smoke run completed with best35. The plain1200-second run is live in this snapshot; its log is complete up to the snapshot instant, with no final result implied. The shared variant was prepared and validated but had not begun its long run at this snapshot. Any later complete run will be saved separately rather than altering these frozen artifacts.

Independent review: counterexample_search checked source invariants and expanded400 randomly mutated genomes per model with seed14772999, comparing scalar88-test semantics and physical gate count; all800 passed. status_audit also checked200 shared/dirty warm starts on all94 raw extremal tests. These are implementation checks, not trusted UNSAT certificates.
