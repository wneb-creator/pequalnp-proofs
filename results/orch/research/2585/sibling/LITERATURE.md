# L2585 literature and weaker charge audit

Read date: 2026-11-25. All literature accessed through the read-only web tool, not container downloads. No applicable published proof or C4-free bipartite counterexample was found. **UNVERIFIED:** that the precise L2585 statement remains open in the entire 2026 literature; search cannot establish absence. The sources below support only the stated narrower facts.

## Exact relationship to known models

Jukna, *Notes on Boolean Read-k and Multilinear Circuits*, revised 2023, Theorem 1: for homogeneous monotone functions, minimum read-1 circuit size equals minimum monotone arithmetic circuit size for the associated monomial support. This matches the repository proof-tree notion. Thus L2585 would establish a Boolean-to-arithmetic size-preserving conversion for C4-free bipartite quadratic functions; generic homogeneous arithmetization is insufficient. Source read: https://arxiv.org/html/2207.08701v3 (Theorem 1 and Section 5.1).

## Single-level counterexamples and scope

Jukna, *Disproving the Single Level Conjecture* (2006), Theorem 2.1 uses saturated extensions of Sylvester-type bipartite graphs: both color classes become cliques, so the resulting graphs are explicitly nonbipartite. Page 10 discusses the single-level C4-free lower bound; Problem 8.2 on page 16 asks for a superlinear unrestricted monotone circuit bound for an explicit quadratic graph function. This historical open-problem statement does not certify current status. Source read: https://web.vu.lt/mif/s.jukna/ftp/single1.pdf .

Krapivin, Przybocki, Subercaseaux, *Near-Optimal Encodings of Cardinality Constraints* (SAT 2026), Section 3.4 gives smaller unrestricted monotone circuits for threshold-2 than single-level circuits. Threshold-2 is the complete graph function, so this also does not satisfy bipartiteness or C4-freeness. Source read: https://drops.dagstuhl.de/storage/00lipics/lipics-vol377-sat2026/html/LIPIcs.SAT.2026.23/LIPIcs.SAT.2026.23.html .

## A precise lower-bound method that does not yet transfer

Tarjan, *Complexity of Monotone Networks for Computing Conjunctions*, Stanford technical report STAN-CS-76-553 (1976), Theorem 7 on printed page 16: when required conjunction supports pairwise intersect in at most one variable, any monotone multiple-output network needs the sum of support sizes minus the number of outputs in AND gates. Duality gives the exact analogous OR bound for Boolean sums. Theorem 8 applies this to projective-plane lines. The proof replaces the network by unions and free subset operations, then charges each union to its unique target support. The paper is primary research, accessed as a scanned institutional report mirrored at https://ftpmirror.your.org/pub/misc/bitsavers/pdf/stanford/Stanford_CS_TR_Collection_2025-12-12/OCR/CS-TR-76-553-ocr.pdf .

Possible route, **UNPROVED**: transform an incidence-function circuit into a multiple-output network computing all neighborhood sums with a sufficiently tight budget, then apply the set-network charging argument. Duplicating the original circuit once per cofactor is too expensive. The needed simultaneous cofactor/derivative conversion is exactly where unrestricted Boolean idempotence and absorption intervene; no valid size-preserving conversion was found.

Jukna, *On Graph Complexity* (2006), Theorem 7.3 gives triangle/C4-free formula and circuit-depth bounds, not unrestricted circuit-size bounds. The distinction matters: unfolding a DAG into a formula can increase size. Source read: https://eccc.weizmann.ac.il/report/2004/005/revision/1/download/ .

## Checked local bounds weaker than Read1

- `lean/PEqualNP/Outside/L_meta_3706.lean:1515` (1662 lines): define U as edges whose output has no read-1 proof (`Core.ReadTwiceAt`). For every C4-free AO2 circuit computing the graph function and minimum vertex cover K of G minus U, `|E| + |K| <= C.size + |U| + 1`. No Read1, leastness or normal-form hypothesis. This is exact charging on the read-1 part, with the repeated-edge deficit left unpaid.
- `lean/PEqualNP/Outside/L_meta_2235.lean` (1770 lines): assuming singleton and nonedge-pair rejection, obtains a vertex cover of the accepted read-1 edge subset and charges its size plus edge count against C.size+1. No full-function correctness or global Read1 premise.
- `lean/PEqualNP/Outside/L_meta_2240.lean` (5-line closure through L3557/L2672): projective-plane circuits satisfying the weaker IsSingleRead condition obey `N*q <= 32*C.size + 3*N`. IsSingleRead means one endpoint can be read once; it is weaker than the joint ReadK1 condition and the numerical conclusion is much weaker than the exact star-cover budget.
- `lean/PEqualNP/Outside/L_meta_4183.lean`: least top-form circuits satisfy a cost inequality with explicit unstarred-edge, dirty-AND, centerless-top and OR deficits; this still requires controlling the residual terms.

The optimizer received the exact L3706 statement and is examining possible compensation from leastness and normal form. No additional exact unrestricted cover-cost theorem was found in the local checked files.

## Follow-up on derivatives and semi-disjoint forms

Lingas and Persson, *Improved Lower Bounds for Monotone q-Multilinear Boolean Circuits* (2023), explicitly identify q-multilinearity with the read-q notion. Their semi-disjointness definition requires every individual output polynomial to use each variable in at most one monomial. A one-output incidence function with a degree-two vertex fails that condition. Their exact AND-gate lower bound assumes q=1; the general q bound loses a factor q^4. These results therefore do not furnish the missing unrestricted normalization. Source read on 2026-11-25: https://arxiv.org/html/2305.07364v1, Section 2 definition and Sections 1/3 discussion.

Jukna's author note on simultaneous derivatives states the arithmetic Baur-Strassen/Morgenstern conversion with size at most 5s, including its monotone arithmetic version. It begins with an arithmetic circuit computing the exact polynomial/support. It is not a Boolean cofactor conversion and is not size preserving. Source read on 2026-11-25: https://web.vu.lt/mif/s.jukna/tropical/derivatives.html . My reasoning: arithmetizing a Boolean circuit can replace a valid edge monomial xy by x^2y^2; differentiating and setting the point variables to zero then loses that edge. Thus a direct appeal to arithmetic automatic differentiation assumes away the repeated-variable obstacle.

Lingas's 2018 report abstract gives conjunction-depth versus size tradeoffs for semi-disjoint forms and permits negations only on inputs. It does not claim an unrestricted, gate-count-preserving one-hot conversion. Source read on 2026-11-25: https://eccc.weizmann.ac.il/report/2018/108/ . The downloadable full PDF timed out on the web tool; no claim beyond the abstract is used.
