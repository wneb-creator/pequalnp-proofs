# L-meta-4675 orchestration

Exact posted statement and lease: /tmp/oec/pequalnp-pilot-163/desk-001.json. Only parent holds/renews lease. Reductions closed.

Agents append to own files in results/orch/lemmas; parent summarizes here. Only Mathlib and PEqualNP.Defs allowed in final. Helpers namespace PEqualNP.Outside.L_meta_4675.

Goal: C4-free bipartite edge function, AO2, T(C)=0 implies edge count + vertex-cover size <= circuit size + 1.

## Findings at 2026-11-25 17:13 UTC

- No existing allowed theorem proves the target. ReadK1 bounds require an extra hypothesis; T=0 does not imply ReadK1.
- T=0 is syntactic: AND(x,x) hides x from OR-only reach. A two-gate example disproves the semantic-monochromaticity shortcut.
- Buffer every input with AND(i,i), then shift all original wire references by n: this should preserve AO2 and semantics, add exactly n gates, and make T=0 for every colouring. A draft formal proof is in library-buffer.lean. Thus the target would imply an unrestricted monotone lower bound of |E|+tau-n-1; this is a substantial lower-bound problem.
- Structural endpoint: C4-free rectangles are stars, so a k-rectangle cover gives a vertex cover of size at most k. Missing: extracting such a cover with |E|+k <= |C|+1 despite later AND filters.
- Single-line restriction: monotone f AND g = OR_A forces f=OR_A or g=OR_A. An OR-pruning argument may help charge pairwise-almost-disjoint neighborhoods.
- Essential-variable bound supplies complete star and matching special cases (drafts in semantic-support.lean).
- Exhaustive computational search found no counterexample on 2+3 inputs through all possible violating sizes, or 3+3 inputs through five gates. These searches are not Lean proofs.
- Runtime had no installed Lean or warm Mathlib cache for the active user. Installed verified pinned elan and Lean 4.36.0; downloading pinned prebuilt Mathlib cache, never building Mathlib from source.

Only sources explicitly listed in validation.txt have compiled. No exact target proof and no accepted checker result yet.

## Replan at 2026-11-25T17:26:33.390071+00:00

The complete target remains unproved. Current proof chain: choose a size/AND-pair-minimal T0 circuit (checked); preserve T0 during false-wire folding (generic builder checked, deletion wrapper pending) and top-form lifting (redirect reach lemma underway); classify the earliest dirty AND; eliminate or charge dirty rectangles; apply checked pair-clean lower bound and checked exact bipartite bridge. The dirty-rectangle step is still open.

Counterexample searches: no witness found on <=6 inputs; independent 2+2 brute-force cross-check agrees. Fano 26-gate synthesis and C6 optimal-dirty SMT are ongoing. Failed searches are not proofs.
