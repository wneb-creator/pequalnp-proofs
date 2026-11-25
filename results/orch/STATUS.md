# L-meta-2602 research status

Updated 2026-11-25T04:25:38.256660+00:00. KIT-MESSAGE-ID msg-07569722ae629e1f3149d063.

**The posted gap remains unproved and unrefuted. No proof PR has been opened.**
The canonical file contains checked helper lemmas only; it deliberately does not claim the missing theorem. The local checker reports `REJECTED (no-theorem)`.

## Preserved results

- `lean/PEqualNP/Outside/L_meta_2602.lean` combines the checked components in the required auxiliary namespace. It is a partial research artifact, not a valid final proof submission.
- The exact 65-gate construction has the full incidence semantics, legal distinct earlier binary operands, and both zero derivative traces. Its gate count is outside the posted 63–64 range, so it is not a counterexample.
- Geometry: 52 incidence edges, no rectangle, degree four, and the cover lower bound 16 when neither whole bipartition side is selected. The deleted-endpoint graph has 45 edges and cover number at least 12.
- Trace recurrence is equivalent to active-path reachability. Under the stated TopForm assumptions, at most one dirty AND active on the marked pair forces a surviving directional trace.
- The pair-clean subcase proves the exact posted nonexistence statement with one added premise: every AND rejects every nonedge pair, including diagonal pairs. Higher-degree dirty assignments are allowed. An unrestricted counterexample must therefore have a genuine forbidden-pair-accepting AND.
- Four clean OR clauses cannot accept three disjoint edges of a rectangle-free bipartite graph. A separate elementary matching lemma gives a vertex cover of size at most two for the entire accepted pair shadow.
- Two independent OR-by-OR rectangles, their clean product, and all their clean literal filters have the stated four-center cover containing the marked endpoints. This applies to explicit parallel rectangles, not arbitrary nested dirty gates.
- The archived SAT-to-Lean pipeline reconstructs a RUP certificate using ordinary kernel proofs, including actual Circuit.wires equations for the 65-gate witness. Only propext, Classical.choice and Quot.sound occur. The archive README explains the formatting conversions required before embedding it in a submitted file.

## What blocks the full statement

1. The posted size bound does not establish TopForm, a two-dirty-gate shape, or pair cleanliness. Choosing an ordinary minimum circuit or normalizing it does not automatically preserve the two zero traces.
2. The rectangle cover does not count direct literal-star terms inside the same clean roots. Nested dirty gates and three or more dirty gates are outside that argument.
3. A cover containing both marked endpoints need not satisfy the mixed-cover premise: it may contain a complete bipartition side. No AND-count conclusion of 14 has been proved from the four-center result.
4. No unconditional OR lower bound of 51 for arbitrary dirty circuits was obtained. The existing pseudoforest, ReadK1 and clean-gate results have extra hypotheses. The first-OR induction reduces to the unresolved case of two singleton operands with shared downstream gates.

## Search evidence and limits

Exact local SAT windows exclude several specific one- and two-star replacements. Larger windows timed out. A separate 65-gate plane witness uses 14 AND and 51 OR gates. A 12-gate bipartite tree witness shows that generic AND/OR count equalities alone do not exclude double reread; no ordinary minimality claim is made for that tree.

All 675 fixed theta cores require at least eight injections under the documented source-mask model (558 have bound eight; 117 have no such cover). This is not a lower bound for arbitrary circuits. Mutation and pruned semantic-DAG searches found no 64-gate witness and are inconclusive. Two bounded theta3 OR-count SAT tests also timed out; their ordinary 12-gate positive control passed.

Complete programs, logs, witnesses, manifests and independent checks are under `search/`, `finite/`, and `lrat/`. Solver UNSAT claims without a Lean certificate remain computational evidence only. Raw logs preserve original whitespace and full diagnostics.

## Validation and delivery

See `validation.txt` for build metrics, checker output, axiom audits and timing; `TIMELINE.md` for milestones; and `NOTES.md` for the full shared research record. The branch is `pnp/pilot-65` on the fork. All reviewed compiled components are checkpointed there. A future valid PR must remove the research artifacts from its final tree and add exactly the one named proof file with the exact main theorem.

The desk assigned this gap on the first request; null count is zero. L-meta-1035 was inspected first as requested, but it was not the assigned gap. Three live reductions already occupied this step's available reduction slots; no fourth reduction was submitted.

Sub-agents: 6 (status and counterexample search, structural proof, lemma route, finite search, toolchain, independent review).

## Lease interruption

At 2026-11-25 04:31 UTC the desk returned HTTP410, saying the lease had expired or been released. The prior renewal gave expiry04:44:15UTC. The mandated curl diagnostic retry returned the same410; full headers and body are preserved in desk/auto-beat-011-diagnostic.txt. Proof work was paused and all current reviewed results preserved before a new request, following the owner's specific410 instruction. The cause of invalidation is not yet known.

## Last research updates before the lease interruption

A clean eight-input C8 fragment refutes the proposed two-root pair-shadow cover bound of three: it has four AND gates, a matching of four accepted pairs, and both zero traces. It is a subfunction of C8, not its exact graph function; two omitted graph edges absorb higher terms. The exact two-root SAT model remains UNSAT, with its unverified solver certificate archived only as computational evidence. The beam attempt to extend this fragment to the plane found no completed witness. See two-root-independent-review.md and search/finite-search/two-roots/.

Upstream commit d7dd149881faedf1819d7ca0ca51130327f5a9bb contains a new L_meta_1898 proof of an unconditional plane AND-count lower bound of13. Its equality case does not classify pair cleanliness or preserve OR count/traces under normalization. No unconditional OR-count lower bound was found in the182-file refresh. The exact source reference and census are in library-refresh/. The fetched tree still has no direct L_meta_2602 proof file.
