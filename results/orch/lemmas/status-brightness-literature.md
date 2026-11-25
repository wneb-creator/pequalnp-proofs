Primary-source check, read 2026-11-25

No applicable general theorem was found in this bounded search that makes an ordinary minimum monotone quadratic circuit bright on every edge, or that turns our two carrier-consumption positions into a read-two formula. This is a search outcome, not a claim that no such theorem exists. No external statement is used as a Lean axiom.

1. Stasys Jukna, *Disproving the Single Level Conjecture*, author PDF:
   https://web.vu.lt/mif/s.jukna/ftp/single1.pdf
   Theorem 2.1 gives quadratic functions with linear general monotone circuits and almost quadratic single-level circuits. Its examples are saturated extensions of bipartite graphs, with both sides completed to cliques, so this does not refute a special Fano/C4-free normalization theorem. It does rule out relying on a universal single-level normalization. The paper explicitly distinguishes formula length, total circuit gates, and AND-only complexity. The relevant exact phrase is "saturated extensions of Sylvester-type graphs" (page 4).

2. Stasys Jukna, *Lower Bounds for Tropical Circuits and Dynamic Programs*, Remark 10 and Theorem 18:
   https://arxiv.org/html/1406.3065
   Remark 10 distinguishes multi-output linear forms from their single-output bilinear polynomial. For a matrix without a 2-by-2 all-one submatrix, the displayed edge-count lower bound applies to tropical, arithmetic, and multilinear Boolean circuits. The discussion explicitly says the analogous general Boolean bound was not known there: "no such bound is known so far in the boolean semiring." This historical statement is not a claim about all literature as of today. Our unrestricted circuit cannot be treated as multilinear merely because its output is quadratic.

3. Stasys Jukna, *Notes on Boolean Read-k and Multilinear Circuits*:
   https://arxiv.org/html/2207.08701v2
   Read-k bounds variable exponents in at least one arithmetic-shadow monomial for each prime implicant. It does not mean fanout at most k or at most k carrier exits. The text calls these monomials "shadows" and permits other monomials of unrestricted degree. The equivalences for read-one circuits and the read-one/read-two separation therefore do not establish brightness or supply the missing proxy-branch contraction in our p14 case. Inference: translating our carrier structure to the required shadow property would itself need proof.

4. Andrzej Lingas and Mia Persson, *Improved Lower Bounds for Monotone q-Multilinear Boolean Circuits*, abstract:
   https://arxiv.org/abs/2305.07364
   The abstract gives q-multilinear bounds for semi-disjoint bilinear Boolean forms and an AND-count bound for the one-multilinear case. Only the abstract was read in this search. Applicability to our single-output marked-edge condition is UNVERIFIED: neither the required model translation nor an exact 27/28 equality consequence was established.

The useful local route remains to combine the compiled carrier-own-derivative lemma with a first AND creating a marked edge, then analyze how both derivative signals can be lost downstream under the two-consumption and zero-empty-branch constraints. No general formula conversion is assumed. A local double-star example already shows that empty singleton support at every AND plus two consumptions at the two central vertices alone is insufficient; the Fano-wide geometry and budgets must enter.
