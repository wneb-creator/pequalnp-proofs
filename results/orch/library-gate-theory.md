# Gate-count theory investigation for L-meta-2583

Stopped all mathematical/search work immediately on parent notification that the lease was no longer live. Both running search sessions were interrupted with exit130. No desk calls, git writes, or final-file edits were made.

## Proposed split and status

The target lower bound would follow from OR-count >= |E|-1 and AND-count >= matching-number for bipartite C4-free graph functions. Neither statement was proved. My assigned focus was the OR count.

The OR-count statement is dual to a lower bound on AND gates computing the monotone 2-CNF with one clause for each graph edge. Free ORs in that dual model can intersect/filter clause families through Boolean idempotence. The usual homogeneous arithmetic argument does not justify ignoring this effect.

## Search representation

Every circuit with k counted OR gates and arbitrary free AND gates can be flattened so that each OR operand is an AND of a subset of input variables and earlier OR outputs; the final output is likewise such an AND. I implemented this canonical representation in `library-gate-or-search.cpp` and mutation search over its operand masks.

C6 test: seek4 OR gates, violating the proposed5 lower bound. Evaluate all6 true edge assignments and5 maximal independent-set false assignments. Fano test: seek19 OR gates, violating proposed20 lower bound; evaluate21 true edges plus37 maximal-independent-set false assignments. Since candidate circuits are monotone, passing these critical assignments would establish exact function equality on all inputs.

Both searches reached one critical-assignment error, and neither found a zero-error circuit before mandatory interruption. These stochastic searches are not lower-bound certificates. Best circuits and logs are retained beside these notes.

## Literature observation

The project own published note at https://pequalnp.com/papers/note-1 (search result read2026-11-25; direct web open failed) identifies the gap between single-level/multilinear and arbitrary monotone circuits as an unresolved obstacle. It points to Jukna TR05-021 Problem24 and arXiv1406.3065 Remark10. Original papers were not independently opened under this job allowed-host constraint, so the original-paper claims remain UNVERIFIED here. The local notes/note-1-edge-function-exact-size.md confirms this distinction in its literature summary. No applicable existing unrestricted OR-count theorem was found.

Stopped at 2026-11-25T15:08:21.800302+00:00
