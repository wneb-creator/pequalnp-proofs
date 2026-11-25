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


The five-point alias phase completed its703-second cap without a witness.
Cases1 and2 received414,344,605 and421,577,117 proposals, respectively;
their best plain candidates still missed one edge, and dirty candidates
missed three. These numerical plateaus provide no lower-bound evidence.
All five-point workers are stopped and all full logs are archived.

## Eight-point patch

The next geometry selects points[4,5,6,7,8,10,11,12] and all lines except0.
It has20 inputs,32 incidence edges,136 maximal false assignments and no
private line inputs. Its standard star circuit uses39 gates; a38-gate patch
would extend to the full63-gate target with the remaining five point stars
and five OR gates. Independent enumeration confirmed all168 boundary rows.
The39-gate control passed all1,048,576 inputs; its64-gate full extension
passed all67,108,864 inputs.

The three-word evaluator uses class-directed dominance: an earlier wire
with more positive acceptances and fewer negative acceptances can replace
a later wire. Every replacement is materialized by OR(a,a), including the
final output, so emitted circuits match the values checked. A60000-case
random differential check found no lost positive acceptance, new negative
acceptance, emitted-net mismatch or backward-read violation. The initial
normalization result is explicitly checked for zero errors before mutation.

Twenty-eight43-gate nonlinear controls supply genuinely mixed AND/OR
structure via the exact identity pR OR qS =
((p OR q) AND (R OR S)) AND ((p OR S) AND (q OR R)).
The independent reviewer checked every control on all1,048,576 inputs.
The search mixes deleted nonlinear seeds with deleted randomized stars.
Any candidate with zero actual errors is printed immediately, regardless
of optional read-one scoring. The approved frozen source hash is
1695373998f65f4a8f46599789fee94261d2c8bca63aa77b929888ae685872ae.

The seed205608 run began after the parent's16:19:08UTC renewal, with a
1200-second cap and one CPU. The source, exact data, full controls and
verification logs are preserved in results/orch/search2056/eightpoint/.


The first eight-point phase was stopped after the initial seed improvement
became available; its full logs are preserved. No exact candidate appeared.
The next approved source changes only the seed loader to accept41 or43 gates.
Thirty-two41-gate double-star controls use the identity
bA OR bc OR cD = (b OR D) AND (c OR A) AND (b OR c).
All new controls were independently verified on every local assignment.
The combined60 controls pass startup checks. Source hash:
f5e8aa75c1388c87151cd46d461c99702f695df320152b00df660e1e93b36ab1.
The new phase began after the16:22:09UTC renewal and has an absolute deadline
of16:39:08UTC, within the original20-minute allowance. The earlier deletion
heuristic protects the first two gates of41-gate seeds; this only restricts
initial proposal choices, and later mutations can still edit those gates.

The independent emitted-net analyzer records raw false positives/negatives,
live gate count, copies, atomic edge gates, zero-positive profiles and
number of distinct gate functions. Missing one edge is still a failed
candidate and supplies no evidence of a lower bound or eventual success.


Differential-test accounting was refined to distinguish proposals from
valid nets actually checked: the eight-point evaluator checked59,097 valid
nets among60,000 randomized trials; the full-plane adaptation checked9,836
among10,000. Invalid forward-reference mutations were skipped. Repeating
the deterministic tests with explicit counters passed with no discrepancy.
The frozen search sources and their approved hashes did not change.
