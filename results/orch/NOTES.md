# L-meta-1031 orchestration

Lease owned only by root. Other agents must not call desk.

Read /tmp/oec/pequalnp-pilot-56/desk-001.json for exact statement and allowed imports.

Current upstream: 9c4fa2b. Reductions allowed but three already live; assess before proposing another.

Each strategy records findings under a distinct heading. Use own files in results/orch/lemmas; only root edits final lean/PEqualNP/Outside/L_meta_1031.lean.

## Reduction/status strategy

- Time: 2026-11-25T01:09:49.161559+00:00.
- Desk assigns L-meta-1031 with reductions_live = 3. Upstream already has R_meta_1031_1, _2, _3. Current join caps at three live reductions per step, so a fourth is not permitted.
- R_1031_1: useful least circuit (each AND owns an edge), plus an exchange that strictly decreases the count of AND gates owning two disjoint edges while preserving usefulness and not increasing size. Triangle-free pairwise-intersecting edge families are stars.
- R_1031_2: existence of a least circuit where all AND gates are semantically below the graph function, plus cleanup eliminating AND gates with empty ownership while retaining soundness.
- R_1031_3: existence of a least HasStarProfile circuit (empty ownership allowed), plus cleanup eliminating empty ownership preserving profile.
- EXACT reusable second hypothesis of R_1031_2 is checked in L_meta_1906.lean (theorem near line 897). The first hypothesis appears still open (no L_meta_1905 file). L_meta_1600.lean shows a sound AND has star-or-empty ownership in any C4-free graph.
- L_meta_4846.lean proves two disjoint owned edges force an accepted nonedge pair at the gate. This suggests a weaker normal-form target: only pair-soundness, not soundness on all assignments. Pair-soundness plus no triangles implies star-or-empty profile. Need both a least pair-sound circuit and nonempty ownership; neither follows from current source findings.
- L_meta_5355.lean constructs a useful monotone circuit of size at most edge count + vertex-cover cardinality - 1. No general matching lower bound was found; using that bound would assume the unresolved main structure question.
- Import restriction allows only Mathlib and PEqualNP.Defs: outside lemma source must be copied into the single final file if used, not imported.

## Counterexample strategy 2026-11-25T01:10:47.324437+00:00

- Empty graphs including n=0 admit the zero-gate circuit with out-of-range output, so no trivial refutation. Forward references read false; unused/identity/constant gates can be removed from minima of nonconstant edge functions.
- R_meta_1031_2 proves the star conclusion given a minimum circuit with globally sound AND gates and pruning to nonempty owners.
- No installed SAT solver found. A Z3 binary download was attempted, but curl failed before writing bytes when disk had only 26 MB free; abandoned pending toolchain cleanup.
- Plan: exhaustive normalized small circuits for all triangle/C4-free graphs on up to four vertices, then SAT or larger stochastic search if resources permit.

### Small-case circuit census 2026-11-25T01:11:46.541660+00:00

Standalone C++ truth-table search enumerated all binary AND/OR circuits with distinct nonconstant gate functions and no duplicate gate outputs, using earlier distinct wires. Arbitrary references/constants/identities are excluded by standard normalization (not yet Lean-proved), so results are computational evidence only.

- n=4, depth4:81,985 prefixes; all37 nonempty triangle/C4-free labeled graphs found at a minimum size1–4 with every AND owning a nonempty star.
- n=5, depth5:27,160,961 prefixes; all290 nonempty labeled forests found at a minimum size1–5 with every AND owning a nonempty star. Remaining12 cases are5-cycles, lower bound>5.
- Code and full output: scratch counter_small.cpp, counter_n4.log, counter_n5.log.

## Lemma inventory strategy

PEqualNP.Defs gathers 86 definition modules; bounded declaration search found no theorem/lemma declarations in Defs/*.lean. Useful data definitions include coverCircuitB, graphFun, Owns, HasStarProfile. Existing Outside L_meta_539 contains a short Nat.find argument (around line 2738), but no such result is available through the allowed imports.

Created inventory_minimum.lean: generic existence of a minimum AND/OR fan-in-two circuit from any witness. Created inventory_existence.lean: explicit edge-list accumulator construction for every finite graph (including empty graph and n=0). Neither has been compiled yet; waiting for cache readiness and ENOSPC recovery.

## Proof strategy: pair soundness

The full normalization target may be weakened to pair soundness of every AND gate. For n>0, if an AND gate being true on pairInput u v always implies G.Adj u v (u=v included), every AND gate globally implies the graph function. Choose the earliest true AND at an arbitrary input x. Its true inputs trace through OR-only paths to true vertices of x; fan-in at most two supplies a pair. Arity zero or one contradicts pair soundness on u=u. The arity-two case supplies the graph edge. n=0 must be handled separately by the empty circuit.

Uncompiled experiment: results/orch/lemmas/proof_pair_sound.lean, 309 lines. It reuses local wire/cone machinery from checked L_meta_4846, renamed under the task namespace. No theorem imports outside Defs and Mathlib. Awaiting toolchain/cache.

### Five-cycle completion 2026-11-25T01:12:52.612832+00:00

Depth6 normalized census:1,460,469,821 prefixes in20.4seconds; no labeled5-cycle function occurs. A7-gate star circuit is OR(1,4),AND(0,5),OR(1,3),AND(2,7),AND(3,4),OR(6,8),OR(10,9), output11. Together these cover every triangle/C4-free graph on≤5vertices computationally (normalization is not formally established). A separate search found no minimum five-vertex forest circuit with nonstar or empty AND ownership.

Next: stochastic synthesis for Petersen and Fano incidence graphs against all edge inputs and maximal independent sets. For monotone circuits these cases characterize the entire edge function, reducing from2^n assignments to a small truth vector.

## Root literature check (2026-11-25)
Read Stasys Jukna, Disproving the Single Level Conjecture, primary author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf via web tool. General quadratic single-level normalization fails; examples in paper use saturated graphs with cliques, so do not directly refute our C3/C4-free claim. The paper distinguishes formula and arbitrary-fanout circuit lower bounds, which must not be conflated. No confirmed literature proof of the present normalization.

## Scratch storage
The environment had no advertised Lean installation or warm cache. Pinned Lean 4.36.0 was installed under /tmp/oec/pequalnp-pilot-56/lean-4.36.0-linux; due to a 7.9 GB overlay limit, its immutable files are backed by job-specific /dev/shm/pequalnp-pilot-56 and linked at that scratch path. Full Mathlib cache is being restored authentically; checker requires whole Mathlib. No tracked toolchain/configuration file changed.

## Relevance prerequisite (2026-11-25T01:17:57.234771+00:00)

Independent normalization reasoning found no valid whole-region exchange yet. Simple bypass is insufficient: (a∨b)∧(c∨d)∧(a∨c) computes the P4 edge function ac∨ad∨bc but the earliest AND owns disjoint edges; it uses 5 gates versus a 4-gate clean circuit. Sharing among later cleaners is the unresolved issue.

Created results/orch/lemmas/relevance.lean: deletion circuit with missing gate redirected to an out-of-range false wire; semantic proof gives pointwise decrease and equality whenever that gate was false. The final lemma minimum_gate_edge_live says every gate in a least monotone binary circuit computing any graph function is true on some graph-edge pair input. No cycle assumptions. Base wire semantics copied from checked L_meta_1906, renamed into the task namespace. Not compiled yet; cache setup/compile queue pending.

### Larger graph search 2026-11-25T01:21:01.372110+00:00

Exact semantic test compression: a monotone circuit computes graphFun iff it is true at every edge pair and false at every maximal independent set. Petersen has15+15=30 such cases; Fano incidence21+37=58.

Five-minute stochastic searches from canonical star-cover circuits with one gate removed found no exact circuit: Petersen19gates,3,559,004,844 evaluations/74,031restarts; Fano26gates,3,372,699,873 evaluations/69,362restarts. Both best candidates miss one test.

Z35.3.3 installed under scratch(84MB). Dirty-AND queries at canonical optimum: C5k7UNSAT1.26s; C6k8UNSAT9.03s; C5withleafk8UNSAT11.32s. All evidence depends on model normalization and untrusted SAT, not Lean. Sanity C5k7unconstrainedSAT0.35s, full32inputvalidation passed. Its nested-AND circuit is AND01,OR03,OR13,AND(2,7),OR(4,5),AND(6,9),OR(8,10),output11. ANDgate5(in wire10) owns04,34 and inherits01 fromANDgate0. Thus bottom-level-only form is false for arbitrary optima even though AND-soundness survives.

Petersen19and theta(2,3,3)10gateSAT searches underway. Theta graph has7vertices8edges,alpha3,tau4,canonical11gates.

Inventory checkpoint 2026-11-25T01:23:06.373199+00:00: named L_meta_1031.lean generic minimum helper passed lake build (5149 jobs, exit0). Full logs first-partial-build.stdout/.stderr under scratch. No assertion of posted star theorem yet.
