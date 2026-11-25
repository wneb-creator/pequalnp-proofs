# L-meta-2625 orchestration

Assigned as a reduction-only cut. Goal: a useful decomposition of the order-3 plane monotone circuit search with 63 gates. Exact statement is in the scratch statement.txt.

Strategies: symmetry decomposition (reduction_design), constructive gadgets (construction), finite computational checks (finite_checks). Independent review and tooling setup: rules_review.

Toolchain unexpectedly absent despite kit preparation claim; installation is being attempted using permitted official hosts.

## Findings

- L-meta-1035 desk status: not_open; already checked or stood down. No work on it.
- Complete open-PR census: 22 pages, 2105 PRs. PR8889 already proposes prime-implicant geometric-envelope cut for2625; avoid duplicate.
- finite_checks certified468 distinct generic negatives and maximal allowed envelope:52 incidence pairs plus52 collinear point triples plus52 concurrent line triples. The envelope has12234 false inputs, exactly468 maximal false inputs equal to generic negatives.
- Candidate revised cut:7point union-of-two-lines residual (20inputs,33gates target) plus6star completion (29gates plus1 OR). Independently checking plausibility.

## Finite checks (2026-11-25T00:38:42.399773+00:00)

- Reproducible programs and complete results are preserved in `results/orch/finite/`. These are computational sanity checks, not Lean proofs.
- Exhaustive envelope enumeration: 52 incidence edges, 52 collinear point triples, 52 concurrent line triples; 560 caps on each side; 12,234 false inputs; exactly 468 maximal false inputs, equal to the listed generic orbit rows.
- Every one of the 1,716 seven-point subsets leaves some induced maximal false inputs unconstrained. Four classes by (maximal false count, missing count, collinear point triples): (89,44,5) x468; (99,61,7) x936; (101,61,6) x234; (102,66,8) x78.
- Recommended seven-point core is the union of lines 0 and 1: {0,1,2,3,4,9,10}. It uses 20 inputs, has 28 incidence edges and 8 collinear point triples, and leaves 66 of 102 induced maximal false inputs unconstrained. This does not establish existence of a 33-gate circuit.
- Its geometry is a subdivided 3-by-3 complete bipartite graph, two distinguished four-point lines, and two leaves at their intersection point 1. Grid point triples are [0,3,9] and [2,4,10]; grid line matrix is [[12,4,10],[2,3,7],[6,8,9]], distinguished lines 0 and 1, remaining leaves lines 5 and 11.
- A more restrictive 17-input six-point core was considered but not selected: 24 incidence edges, 306 projected negatives, 16 of 52 induced maximal false inputs unconstrained. Its requested 28 gates have no witness.
- `baseline.py` constructs and checks the standard 34-gate seven-point core and 64-gate completed circuit. Checks cover all 28 / 52 required incidence pairs and all 624 listed negative rows (468 distinct). All checks pass. The needed one-gate saving remains an open synthesis hypothesis.

Toolchain setup complete: Lean4.36.0, official Mathlib cache9117artifacts; named reduction builds. First preservation push9f32b1ef5bf80d861d03e59a786d07e57ceccba7. Compiler remapping lemmas independently compile; full compiler remains in progress.
