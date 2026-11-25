# L-meta-2056 full-plane stochastic search

Owner: not_elimination. Parent holds and renews the lease.

The exact posted statement asks for a monotone fan-in-two circuit with at most
63 gates, accepting the52 incidence pairs for (p+l) mod13 in {0,1,3,9}, and
rejecting the two orientations of closure inputs from point subsets of size
at most3. These negatives are exactly all704 maximal false assignments:
378 closures in each orientation, with52 overlaps. Thus agreement on the
posted756 tests implies exact correctness of the full incidence function.

The64-gate control was relabeled from the earlier difference-incidence seed
by negating its line labels. I independently verified all756 tests and then
all67,108,864 assignments with a bit-parallel C++ verifier. The results are
plane2056-control.stdout/.stderr, with a PASS result and no errors.

This route searches the full26-input plane, distinct from the affine43-gate
core search delegated to another agent. It starts with randomized point/line
star circuits and absorption seeds that already have a repeated-read proof
on canonical edge(point0,line0), inputs0 and13. It deletes enough star gates
to reach63 gates, then uses annealing, multiple simultaneous mutations,
fanout redirection, gate permutations and a pool of near candidates.

The engine evaluates all756 posted tests in12 uint64 blocks per wire. It
normalizes each singleton positive-edge profile to that edge's direct AND,
and penalizes zero-positive-profile gates and gate functions equal to primary
inputs. Three-bit flags track joint read1 proof witnesses on the canonical
edge. Any zero-error circuit is reported even if it does not satisfy the
preferred structural objective.

Source: /tmp/oec/pequalnp-pilot-121/not-elimination/plane2056_local.cpp.
Full logs: plane2056-local.stdout/.stderr in that directory.
Verifier: verify_plane2056.cpp there.
Data source: /tmp/oec/pequalnp-pilot-121/plane2056-sat/plane2056-data.json.
Preservation archive: results/orch/search2056/.

Seed205663 started after the parent's15:40:49UTC renewal, with a1200-second
wall-time cap and one CPU. Its startup check passed64 randomized positive
seed controls on all756 posted rows. The initial near hit misses three
positive edges and has no negative errors; this is not a proof or witness.

## Five-point patches

The full-plane phase stopped after331.5seconds and65,009,659 proposals, with
the same three-edge miss. Its complete logs and sources are preserved.

Parent then approved searching23-gate patches on five selected points. A
patch witness extends to the full63-gate target by adding the eight remaining
four-edge point stars and eight OR gates. The distinct supplied point sets
were [0,1,2,3,4], [0,1,2,3,6], and [0,1,2,3,9], with17,16,18 inputs
respectively. No exhaustive automorphism classification is claimed. Each
patch has20 minimal positive rows and32 point-subset closure negatives, and
the exact sum-incidence geometry and all closure rows were recomputed.

The patch engine uses one uint64 per wire. It interleaves a plain fitness
population and a population with a soft preference for any accepted edge
lacking a joint read1 witness; there is no fixed-edge restriction. Joint
read1 witnesses for all edges are tracked in parallel using three bitsets.
Any zero-error candidate is reported regardless of the preferred objective.
Independent review approved the evaluator and exact data. Startup checks
passed192 randomized positive seed controls across the three cases.

The first phase ran about100seconds, giving each case53--59million proposals.
The two-triple case [0,1,2,3,4] was then excluded immediately: the checked
L_meta_5187.core5_lb proves18 gates for its14-edge core, and its six essential
private-input deletions force24 gates for the full patch. The remaining two
cases resumed after the parent's15:52:36UTC renewal. Their plain populations
miss one edge; dirty near hits miss three or four edges and duplicate earlier
wire functions. None is a witness.

The sources, complete phase logs, data and per-case best candidates are in
results/orch/search2056/fivepoint/. A further alias-normalizing evaluator has
been prepared to redirect later uses to the earliest identical test signature
and remove artificial read1 failures from duplicate subcircuits. A60000-case
randomized differential check verified preservation of positive evaluations,
absence of new negative acceptances, agreement with actual mutated circuits,
and backward-read validity. Independent review approved the alias evaluator at
SHA256c6d4be19755db0a4dc8e4d9186dde940e51cdf7af497789c875e7388799e6467.
It began after the parent's15:59:18UTC renewal, with a703-second cap to finish
the original20-minute patch-search budget. Only cases1 and2 are selected.
All actual emitted candidate gates remain in the logs; representative-based
read1 scoring is solely a search preference, and raw-zero is computed from
the actual emitted network on all52 rows.

The extension script extend2056_patch.py is also preserved. It exhaustively
checks a proposed patch, lifts its input indices to the full26-input problem,
adds the eight remaining stars and eight ORs, and writes the resulting circuit.
A24-gate control patch passed all65,536 local assignments; its64-gate extension
then passed all67,108,864 full assignments. This validates the witness pipeline
without claiming a63-gate solution. The Lean packed checker prepared by
gate_elimination is ready to check any actual63-gate candidate.
