# L-meta-2590 stochastic counterexample search

Owner: not_elimination. Only parent holds and renews the lease.

The target lower bound is20 gates for a monotone fan-in-two Petersen circuit.
I seek a19-gate AND/OR circuit. Any candidate must pass independent exhaustive
evaluation on all1024 assignments before Lean proof work.

The exact test set consists of15 minimal true edge masks and15 maximal false
independent-set masks. The latter are
50,69,104,116,138,201,208,276,385,402,521,548,554,770,773.
Monotonicity makes agreement on these30 assignments equivalent to agreement
on all inputs. Existing20-gate positive control base20.txt independently
passed exhaustive evaluation on all1024 assignments.

The search generates randomized minimum-cover star circuits using all five
minimum vertex-cover masks907,822,621,469,250, random orientations of the
three edges inside each cover, and randomized output OR trees. Dirty seeds
replace input0 by the absorption identity 0 AND(0 OR r), preferring r=1,
before removing three ordinary star gates to reach19 gates. Clean20-gate
seeds with one gate removed are also included. A startup control verified128
randomized positive seeds on the complete30-row test set.

The objective tracks joint read1 proof witnesses on the canonical edge(0,1)
using three-bit flags per wire, and encourages that edge to be accepted
without a joint(1,1) witness. This is justified as a necessary symmetry case:
L_meta_6369 and L_meta_2237 prove the general C4-free read1 lower bound
|E|+vertexCover<=size+1, hence at least20 here. I independently generated and
verified an automorphism taking each of the15 edges to(0,1); the permutations
are saved in petersen2590-edge-auts.json. The heuristic still reports any
zero-error candidate even if it does not satisfy the preferred objective.

The engine uses one uint64 per wire, annealing, a pool of near candidates,
multiple simultaneous mutations, whole-gate changes, safe gate permutations,
associative regrouping, and fanout redirection. It uses no NOT gates.

Scratch source: /tmp/oec/pequalnp-pilot-121/not-elimination/petersen2590_local.cpp.
Complete logs: petersen2590-local.stdout and petersen2590-local.stderr there.
Data: petersen2590-data.json and petersen2590-rows.txt there.
Run seed259019 started after the parent's15:18:34UTC lease renewal, with a
1200-second wall-time cap and one CPU. Parent will be notified immediately
of a witness, completion or termination due to a desk error.

The parent later issued a DESK_ERROR stop notice. The search was terminated
immediately with exit143 after192.3 logged seconds and1,001,837,447 proposals.
Its best circuit misses edges(3,4) and(3,8), has no extremal-row false positives,
and accepts the canonical edge without a joint read1 witness. Exhaustive
verification found22 incorrect assignments. This is not a counterexample.
The circuit retains a gate semantically equal to input0, so it is an ordinary
absorption near hit.

A stronger phase was prepared that replaces each singleton positive-edge
profile by its direct atomic AND and penalizes zero positive profiles and
gate functions equal to primary inputs. It was C++-compiled but never launched.
All sources, complete logs, data, automorphisms and best candidate are archived
in results/orch/search2590/. No child-owned processes remain active.
