# Post-2018 research audit for L-meta-3566

Read date: 2026-11-25 UTC. All research used the built-in read-only web tool; no shell network requests and no external code execution.

Outcome: no post-2018 theorem or counterexample establishing/refuting the exact unrestricted monotone bound `|E| + tau(G) - 1` for C4-free bipartite graph edge functions was found. This is a search result, not proof that the problem remains open worldwide. **UNVERIFIED:** the global claim that no such result exists.

## Direct baseline

Stasys Jukna, *Lower Bounds for Tropical Circuits and Dynamic Programs*, arXiv:1406.3065v2, Remark 10:

https://arxiv.org/html/1406.3065v2

The remark explicitly distinguishes the multioutput linear map associated with a Boolean matrix from its single-output bilinear polynomial. It states that the analogous edge-count lower bound for the unrestricted Boolean semiring was not known, while restricted fanout-one, tropical, and multilinear Boolean bounds were available. The abstract page dates this version to 2014-07-29; the journal reference is Theory of Computing Systems 57:1 (2015), 160–194. This historical statement alone does not establish current status.

## Confirmed newer restricted result

Andrzej Lingas and Mia Persson, *Improved Lower Bounds for Monotone q-Multilinear Boolean Circuits*, 2023:

https://arxiv.org/html/2305.07364v1

The abstract and section 4 establish at least p AND gates for 1-multilinear circuits computing semi-disjoint bilinear forms with p prime implicants, and size Omega(p/q^4) for q-multilinear circuits. Section 1 still presents an unrestricted Omega(p) bound for those forms as a challenge. The paper's section 2 defines semi-disjoint forms with each variable in at most one monomial of each individual output: an arbitrary single-output graph edge function is not generally of this type. This result cannot directly establish the requested exact lower bound, and its q restriction cannot be silently dropped.

## Explicit C4-free construction, but a different semantic task

Lianna Hambardzumyan, Hamed Hatami, and Ndiame Ndiaye, *On depth-3 circuits and covering number: an explicit counter-example*, 2022:

https://arxiv.org/html/2210.08300v1

Theorem 2.1 constructs n-by-n matrices with Omega(n^(4/3)) zero entries, no all-zero 2-by-2 submatrix, and an O(log^4 n) rectangle cover of the one entries. Equivalently, complements of certain C4-free bipartite incidence graphs have small rectangle covers. This concerns graph representation/CNF complexity, whose pair-input agreement is weaker than computing the full monotone edge function. It is not a counterexample to the current Lean statement.

Jukna's January 2024 author commentary connects this to the graph/CNF formulation and explains the construction:

https://web.vu.lt/mif/s.jukna/boolean/CNF.html

## New multilevel upper-bound technique, outside the graph class

Andrew Krapivin, Benjamin Przybocki, and Bernardo Subercaseaux, *Near-Optimal Encodings of Cardinality Constraints*, arXiv:2603.28954v2, 2026-04-16:

https://arxiv.org/html/2603.28954v2

Section 3.4, Theorem 6 gives a monotone circuit for threshold-2 with `2n + sqrt(2n) + O(n^(1/3))` gates. Its comparison with single-level lower bounds establishes that smallest circuits need not be single-level even for threshold-2. Appendix A.2 uses a threshold-3 circuit internally. Here the edge function belongs to the complete graph K_n, which is not bipartite/C4-free for the relevant n. This supplies possible construction inspiration but no transfer to the target has been proved. Certificate-search agent was notified.

## Other sources inspected

Jukna's book updates through July 2024:

https://web.vu.lt/mif/s.jukna/boolean/comments.html

The updates include the explicit CNF construction above and monotone-arithmetic/real-circuit results, but no identified resolution of the unrestricted single-output C4-free edge-count bound.

Jukna's 2022 read-k note was opened, but follow-up PDF searches timed out; no new quadratic/C4-free implication was established from it:

https://eccc.weizmann.ac.il/report/2022/094/revision/2/download/

Searches used exact combinations of C4-free, K2,2-free, quadratic Boolean functions, single-output bilinear, monotone circuits, and vertex cover, with recent-year and primary-source filters. Broader graph-property lower bounds (matching/clique) and arithmetic homomorphism-polynomial bounds were excluded because their input/functions differ from this fixed-graph vertex-input edge function.
