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


The eight-point phase completed its original wall-clock budget at16:39:07UTC.
Its final v2 run exited0 after991 seconds and 548551246 proposals.
No witness appeared; the plain candidate still misses one edge and the
nonlinear candidate misses three. Both have38 live distinct gates; the
nonlinear candidate has9 AND gates and29 OR gates. All complete logs and
normalized circuit analyses are archived; no eight-point worker remains.


## Full-plane dominance phase

After the parent's16:38:49UTC renewal, the independently reviewed63-gate
full-plane engine started with seed205613, one CPU and a1200-second cap.
It uses12 words per wire for all52 positive and704 negative boundary rows.
The52 exact66-gate double-star controls supply the nonlinear seeds. The
separate inverse-hoist65-gate family intentionally breaks this engine's
normalization heuristic and remains in the exact-state portfolio.
The frozen engine hash is
9e1f96cc68f1786ea1880ec77baf78893ff53dcf2585e903b79ea2d6b100f672.
All source, exact data and validation logs are in
results/orch/search2056/full-dominance/; no exact candidate is yet claimed.


The optional theta-core lifting helper is preserved in search2056/theta-lift/.
It requires, for each of the four arm points b_i, an explicit b_i AND R gate
with an OR-only path to output. Under this checked structural condition,
inserting its two private line inputs into R costs exactly two OR gates per
point. Arbitrary theta circuits do not automatically have this property.
The existing16-gate control passes all1024 core assignments and becomes a
24-gate patch passing all262144 assignments, then a64-gate full control
passing all67108864 assignments. A qualifying15-gate candidate would lift
to23 and63 gates, but no such candidate has been found.


The full-plane66-seed phase completed its1200-second cap and exited0.
It tried 295050948 proposals without an exact witness; best actual
errors remained one and three missed edges, with no false positives.
The complete source, logs, data and actual-network analyses are frozen in
search2056/full-dominance/. No worker from this phase remains.


## Protected shared-AND phase

The next phase uses the audited52 double-star66-gate controls plus468
67-gate controls with one dirty AND reused along two downstream AND paths.
During initial deletion only, the latter protect their dirty input cone,
both immediate consumer paths, their join, and an OR-only path to output.
This marks19 gates; the final output is independently never deleted.
Later mutations remain unrestricted, and actual zero-error reporting is
unchanged. No expanded or composite seed families were added.

Independent review approved source
285ef7eeb40727455eab97ac5f215a04ac0821dae77f39a02b44b65e38b880ea
and configuration
7ef88072d2828cd6a904a04b3977037798ddc32d1eeefb44b236b4c2cc3734eb.
All128 randomized and520 loaded controls pass their complete boundary.
A further8320 deleted-net test passes: every one of7488 reused-seed cases
retains both dirty paths before normalization, and all cases preserve
backward reads, actual emitted-net evaluation, positive acceptance and
absence of new negative acceptance through normalization.

The parent renewed at17:06:14UTC. Seed205614 started at
2026-11-25T17:06:37.490565+00:00, with1200seconds and one CPU. Source and
seed pool are frozen for the phase. Complete preservation artifacts are
in search2056/reused-dominance/. No witness is yet claimed.


## Prepared stratified successor

A successor adds a third population restricted to a live, positive-profile
AND that accepts an actual negative boundary row and reaches two distinct
positive-profile first-AND consumers through zero or more OR gates. Every
AND stops path propagation. The negative-row condition is the definition
of dirtiness relative to this target; absence of singleton acceptance is
not sufficient and is not used. The first two populations retain the
existing plain and non-read1 scoring. All zero-error checks precede class
filters, and final retained pools are exported for finite combinations.

The loader accepts66/67/69-gate controls, with the old520-control prefix
unchanged and104 independently audited nested69 controls appended. Guards
for the latter follow actual metadata: dirty input cones, first-AND paths,
and OR paths from exposed frontier gates to output. They mark23--26 gates.
The19653-case differential check passes, including9152 shared-path and1664
nested-path preservation cases. Actual-dirty reuse counts independently
match negative-row truth evaluation and explicit graph traversal.
The source/config/control archive is search2056/stratified/. The current
protected-only search remains unchanged until the parent authorizes a
reviewed switch after renewal. No target witness has been found.


The protected shared-AND phase completed its1200-second allowance and
exited0, with 309784519 proposals and no exact witness. The complete
emitted best-history nets and full logs are frozen in reused-dominance/.
Its unchanged source did not export internal populations; those memory
pools cannot be recovered after exit. Every actual zero-error candidate
would have been printed before pool insertion. The successor adds final
population export. No worker from the completed phase remains.


The combined624-control successor received final independent approval.
The parent renewed at17:27:01UTC; seed205616 began at
2026-11-25T17:27:56.745856+00:00 for1200seconds on one CPU. Source and
configuration remain exactly at the reviewed hashes. Early independent
checks confirm all three populations: plain misses one edge, non-read1
misses three, and the shared-dirty class misses four while retaining one
actual dirty AND with two relevant first-AND consumers. No witness exists
in the observed output. Error and class metrics agree with independent
emitted-net truth-table and graph-traversal checks.

The independent analyzer now includes all reported modes and final pool
records. It recomputes actual errors and sharing from the emitted network;
reported-label mismatches are diagnostic fields, so they cannot suppress
an actual zero-error candidate. Reviewed source and completed validation
records are preserved in search2056/stratified/; active run logs remain in
scratch, with repository prefix snapshots to be replaced by the full logs
at completion.


The three-stratum phase completed its1200-second allowance and exited0.
It tried232133634 proposals; best errors were1/3/4 missed edges with0
false positives. All20 retained networks are exported (9 plain,4 soft
non-read1,7 shared-dirty). Complete logs and independent analyses are now
frozen in search2056/stratified/, replacing the earlier prefix snapshots.
No witness, error-metric mismatch or class violation was found.

The four-stratum successor additionally retains two actual dirty shared
ANDs connected by a first-AND frontier edge. Its initial63-gate network
has6 missed edges,0 false positives, two shared dirty ANDs, one nested
pair,63 live distinct functions and no earlier directed dominator.
Source b348bd725715fb7c11ccec7e32c8e4a67f70c592790827f5228629124e7c9d20
and the unchanged624-control config were independently approved after
19653 reference checks, including2259 nested-sharing cases. All raw-zero
checks precede population filtering. Parent renewed at17:50:44UTC; the
1200-second one-CPU run began2026-11-25T17:51:22.938004+00:00, with planned
finish18:11:22.938004UTC. Source and seed pool are frozen for this phase.
Source/validation records are complete in search2056/nested-stratified/;
active-run logs and analyses there are explicitly labelled prefix snapshots.


The four-stratum phase completed at18:11:23UTC and exited0 after
1200.02seconds/265012058 proposals. Best-ever errors remained1/3/4/6,
all false negatives. All148 retained networks were exported (7/6/7/128
by mode), and independent replay found no error/class discrepancy. The
retained-pool minima are1/4/4/9, distinct from the best-ever history.
Complete logs, pools and the independent audit are now preserved in
search2056/nested-stratified/ and were pushed in checkpoint c71da7d6.

The next authorized worker is a restricted AND-structure SAT model with
K16 records and cap63. If M counts operand/output memberships and A counts
active records, independently constructing all operand ORs costs at most
M−A−1; the counter enforces M+(16−A)≤80. Source0b7a5652 and nested warm
model00bdaeb5 were independently reviewed with native64-gate controls and
complete clause/model replay. Native start was18:12:24.026UTC with a
3600-second limit and original observed deadline19:12:24.026UTC.
The regenerated target CNF exactly matches c8db4692.

A temporary publication block caused SIGSTOP at18:23:55.564UTC. After
parent-confirmed recovery and lease renewal, the identical process resumed
with SIGCONT at18:24:59.220UTC, a63.655814-second pause. No source/model,
process identity or timeout limit changed. The paused interval snapshot
and resume event are preserved under andcount2056/budget-run/. Live full
logs remain in scratch; no final model or verdict exists as of18:32UTC.

Two separately reviewed successors are prepared but have not had long
target runs. The profile-only source dd56f642 requires nonzero positive profiles
for active records and direct edge ANDs for singleton profiles. The
normalization argument preserves positive behavior while decreasing
negative behavior and membership cost. The weaker-prefix source1acc9485
adds active-prefix/output-active/first-left0 constraints, justified by
compaction, dropping inactive references and an incidence-preserving
input permutation. It has
no right13 or disjointness condition. The stronger split-edge anchor was
withdrawn because overlapping operands can accept an edge through one
shared endpoint. The normalizer and actual transformed controls were
independently checked. Sources, complete controls/logs and exact CNF
regeneration metadata are in andcount2056-profile/ and andcount2056-prefix/.
No63-gate witness or full refutation has been established.
