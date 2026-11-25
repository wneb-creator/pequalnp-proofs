# Literature check for L-meta-2583

Read date: 2026-11-25 UTC. Researcher: checker_audit. Read-only web research;
no external posts, no cache expansion, and no claim that this is an exhaustive
literature survey.

## Result and relevance

I did not find a published circuit beating the star construction for PG(2,3),
or a theorem that converts an arbitrary monotone circuit for a projective-plane
edge function into a read-1 circuit without increasing its gate count. This is
a search result, not a proof that no such result exists.

The most relevant verified theorem gives a cost-free conversion only when the
starting circuit is already multilinear. Published counterexamples to broader
normalization claims use graphs outside the bipartite, C4-free plane family.
In particular, a new SAT 2026 construction improves threshold-2 circuits, but
threshold-2 is the edge function of a complete graph.

The team's local construction and lower-bound work gives the target 64 gates
at q=3: N=13 and N(q+2)-1=64. This number is arithmetic applied to the local
Lean target, not a numerical claim obtained from the papers below. No 63-gate
PG(2,3) circuit was found in the sources actually read.

## Jukna: Boolean read-k circuits (published 2025)

Primary source: Stasys Jukna, *Notes on Boolean Read-k and Multilinear Circuits*,
Discrete Applied Mathematics 360 (2025), 307-327.

- Author PDF, read 2026-11-25:
  https://web.vu.lt/mif/s.jukna/ftp/readk-submit.pdf
- Publisher abstract and publication metadata, read 2026-11-25:
  https://www.sciencedirect.com/science/article/abs/pii/S0166218X2400413X
- DOI: https://doi.org/10.1016/j.dam.2024.09.023

The definition of read-k uses existence, for each prime implicant, of a
syntactically produced monomial with the same support and every exponent at
most k. This matches the relevant meaning of ReadK much more closely than
input fanout or read-once formulas.

Theorem 3, author PDF pp. 11-12, compares multilinear DeMorgan circuits,
multilinear monotone circuits, and read-1 circuits. A multilinear circuit for
f admits a no-larger read-1 monotone circuit for the upward closure of f; this
is f itself when f is monotone. The starting multilinearity assumption is
essential to this theorem and is absent from L-meta-2583.

Short quotation, p. 2: "Read-2 ... circuits can be exponentially smaller than read-1".
The paper's Section 8 supplies a general separation; it does not state a
projective-plane or quadratic-function separation. Thus the general theorem
cannot close the current gap.

## Jukna: tropical lower bounds (2014)

Primary source, version 2 dated 2014-07-29, read 2026-11-25:
https://arxiv.org/html/1406.3065

Remark 10 explicitly separates a matrix's many linear outputs Ay from its
single-output bilinear polynomial f_A(x,y). It states that the usual
forbidden-all-ones-submatrix lower bound for Ay does not immediately give a
Boolean lower bound for f_A. Short quotation from that historical statement:
"no such bound is known so far in the boolean semiring".

For a (k,k)-free matrix, the same remark gives |A|/(2k^3) for tropical,
multilinear Boolean, and monotone arithmetic circuits. At k=1 this is the
C4-free setting. These are restricted models; transferring the bound to
unrestricted Boolean circuits would assume the missing normalization.

This is a verified statement about the 2014 paper, not a claim that the
literature is unchanged through 2026.

## Jukna: the single-level conjecture (2006)

Primary author PDF, read 2026-11-25:
https://web.vu.lt/mif/s.jukna/ftp/single1.pdf

Theorem 2.1 gives quadratic functions with linear monotone circuits and much
larger single-level circuits. The graphs used are saturated extensions of
bipartite Sylvester-type graphs: both bipartition sides become cliques.
Short quotation from the definition on p. 4: "a (non-bipartite) graph".
Consequently this construction cannot be inserted directly as a counterexample
to the plane incidence statement.

Problem 8.2 asks for a superlinear unrestricted monotone circuit lower bound
for an explicit quadratic function. This explains the severity of the desired
normalization but is historical evidence only. Also, representing a graph on
two-element input sets is weaker than computing its edge function on all
subsets; the paper repeatedly distinguishes these tasks.

## Lingas-Persson: q-multilinear circuits (2023)

Primary source, version 1 dated 2023-05-12, read 2026-11-25:
https://arxiv.org/html/2305.07364v1

Theorem 4.1 gives p AND gates for a read-1 circuit computing a semi-disjoint
bilinear Boolean form with p prime implicants. This must not be applied to
the plane edge function. In Section 2, a form is a set of outputs, and the
first semi-disjointness condition says that within each individual output,
each variable occurs in at most one prime monomial. Short quotation:
"at most one monom of the polynomial containing z".

A plane point variable participates in q+1 monomials of the single output,
so that condition fails. Boolean matrix product and vector convolution are
the paper's examples. Theorem 4.3 also uses a size-increasing transformation
and gives an asymptotic restricted-circuit bound, not cost-free normalization.

## Krapivin-Przybocki-Subercaseaux: threshold-2 (SAT 2026)

Primary proceedings article, read 2026-11-25:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol377-sat2026/html/LIPIcs.SAT.2026.23/LIPIcs.SAT.2026.23.html

Andrew Krapivin, Benjamin Przybocki, and Bernardo Subercaseaux,
*Near-Optimal Encodings of Cardinality Constraints*, Section 3.4, Theorem 9:
threshold-2 has a monotone Boolean circuit with
2n + sqrt(2n) + O(n^(1/3)) gates. The article compares this with the corrected
single-level lower bound 2n + 2 sqrt(n+11) - 10. Short quotation:
"the smallest monotone boolean circuits ... are not single level".

This is current evidence that a natural quadratic function benefits from
multiple AND levels. The threshold-2 graph is complete and therefore has
triangles and C4s. The result does not supply a plane circuit, and single-level
and ReadK are different definitions; no direct read-1 separation is inferred
here without an additional argument.

## Limits and next useful work

Targeted searches included projective-plane monotone circuits, PG(2,3),
bipartite quadratic functions, C4-free circuits, and current read-k papers.
They found no verified q=3 or higher-q construction relevant to this gap.
The numbers in the cited theorem statements above were confirmed on pages
actually read. Exact optimal unrestricted gate counts for PG(2,3) or larger
planes are UNVERIFIED: no primary source establishing them was found.

The current pequalnp note was found by search at
https://pequalnp.com/papers/note-1 but repeated direct web opens failed.
Its complete text and date are therefore UNVERIFIED in this note. Its indexed
excerpt pointed to Jukna 2014, whose relevant Remark 10 was read directly.

Useful remaining routes are a finite circuit counterexample search, or a
new plane-specific gate-counting argument. Reusing a theorem for arithmetic,
tropical, multilinear, multi-output, or single-level circuits without proving
the missing conversion would not establish L-meta-2583.
