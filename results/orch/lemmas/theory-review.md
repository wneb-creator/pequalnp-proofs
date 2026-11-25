# Heawood circuit lower-bound theory review

Read and checked on 2026-11-25 UTC by constructive. This is a literature and source review, not a new Lean proof. No desk, build, or git action was performed for this review.

## Finding

I found no applicable theorem giving an unrestricted 27-gate lower bound for the exact single-output Heawood edge function. The repository proves 27 under additional circuit restrictions. The literature explicitly warns against transferring results between formulas, graph representation, arithmetic circuits, and arbitrary monotone Boolean circuits.

UNVERIFIED: that a size-preserving normalization theorem for all bipartite, C4-free quadratic Boolean functions is known, or that it is a recognized open problem in that exact form. Neither claim was established by the primary sources read. Absence from this search is not evidence of nonexistence. The exact 26-versus-27 Heawood question therefore remains unresolved by this review.

## Repository statements checked directly

The target is the disjunction of the 21 edge terms on 14 inputs, with binary AND/OR gates and total gate count. Seven degree-three stars give 27 gates: 14 OR gates inside stars, seven AND gates, and six OR gates joining stars. This construction is both a formula and a single-level circuit.

In `lean/PEqualNP/Outside/L_meta_1983.lean`:

- `pairCleanBound`, line 842, applies to C4-free graphs. Its additional hypothesis says that every AND gate accepts no target-false assignment of weight at most two. It concludes that a vertex cover T exists with `edgeFinset.card + T.card <= gates.length + 1`.
- The Heawood graph has 21 edges and minimum vertex-cover size seven, giving 27 under this hypothesis.
- `core`, lines 1268–1272, and the final theorem at line 1346 assume `ReadsBack 14 C` and prohibit any AND gate from lying in another AND gate's input cone. Their conclusion is `27 <= C.size`. This is the single-level restriction, not an unrestricted theorem.

`L_meta_1483.lean`, lines 1057–1058, proves an unconditional 20-gate bound for the cyclic Heawood presentation. Its introductory explanation identifies the bound as `14 + 7 <= size + 1`. `L_meta_5670.lean`, line 5371, also records a 20-gate bound for another explicit Heawood presentation. I did not recompile these existing files or prove the relabeling between their edge lists and the assignment's list.

Thus every 26-gate witness must escape the existing pair-clean and single-level arguments. In particular, nested AND gates are necessary. After the usual constant simplifications, some AND gate must accept a nonedge pair and later be filtered.

## Primary sources and their actual models

All links below were read on 2026-11-25. No numerical result is being inferred from an unread search snippet.

### Jukna, Disproving the Single Level Conjecture

[Original ECCC TR05-021 PDF](https://eccc.weizmann.ac.il/report/2005/021/download/), especially pages 1–4, 7, 9 and 15.

Theorem 4 disproves same-size single-level normalization for general quadratic Boolean functions; its examples are saturated extensions of Sylvester graphs, not bipartite Heawood graphs. Graph representation checks edge and nonedge pairs, leaving other inputs unrestricted. Exact computation is recovered for particular saturated extensions, which add cliques inside both parts. That argument does not apply to Heawood. Lemma 11 identifies single-level AND-count with biclique-cover number, not unrestricted total gate count. The cited Mirwald–Schnorr normalization concerns GF(2) quadratic forms, XOR/AND, and AND-count only. The C4-free edge-count bound discussed in the circuit section is explicitly single-level. Problem 24 asks, historically, for superlinear bounds for explicit quadratic functions with arbitrary fanout; I did not verify its current status. The paper establishes that unrestricted accounting is difficult, but does not establish that this specific Heawood normalization is open.

### Jukna, Boolean Function Complexity, public early draft

[Public draft PDF](https://web.vu.lt/mif/s.jukna/boolean/bool-V7.pdf), section 7.2, Theorem 7.2, printed page 203 / PDF page index 209.

The triangle-free, C4-free bound is `L_+(f_G) >= |E|`, where the measure is monotone formula leafsize. For Heawood, this gives at least 21 leaves, hence at least 20 internal gates in a binary formula. It supplies neither 27 gates nor an arbitrary-DAG circuit bound. Fanout sharing prevents transferring a formula-size lower bound to circuit size merely by unfolding a circuit.

### Krapivin, Przybocki and Subercaseaux, Near-Optimal Encodings of Cardinality Constraints, SAT 2026

[Publisher HTML, section 3.4](https://drops.dagstuhl.de/storage/00lipics/lipics-vol377-sat2026/html/LIPIcs.SAT.2026.23/LIPIcs.SAT.2026.23.html).

Theorem 9 gives threshold-2 circuits with `2n + sqrt(2n) + O(n^(1/3))` gates. The paper compares this with a single-level lower bound and concludes that optimal threshold-2 circuits need not be single-level. It explicitly distinguishes Krichevskii's optimality result for formulas. This matters because the original 2005 PDF has a sentence about complete graphs that could otherwise be misread as a circuit normalization theorem. Threshold-2 is the complete-graph edge function; this 2026 result does not answer the bipartite, C4-free Heawood case.

### Jukna, Notes on Boolean Read-k and Multilinear Circuits, 2023 revision

[Full primary HTML](https://arxiv.org/html/2207.08701v3), Definition 2 and Theorem 1.

A Boolean circuit is read-1 when its formal polynomial, obtained by OR-to-addition and AND-to-multiplication, contains a squarefree monomial for every prime implicant. This is a restriction on the circuit, not merely on the function. Theorem 1 equates minimum read-1 size for homogeneous functions with minimum constant-free monotone arithmetic size for polynomials having the same monomial support. The paper also separates read-1 and read-2 circuits exponentially. Thus a homogeneous multilinear target alone does not justify arithmetic normalization. Its explanation identifies Boolean multiplicative idempotence and absorption as the source of the distinction. This conditional same-size result is useful, but does not remove the read-1 premise.

## A conditional consequence for search

The following is my mathematical inference from the read-1 theorem and repository theorem; it is not Lean-formalized here.

Suppose a 26-gate target circuit were read-1 after constants and unused gates were removed. The cited theorem would produce a constant-free arithmetic circuit of at most 26 gates whose polynomial has exactly the edge monomials, with positive coefficients. Prune unused gates. A multiplication gate below another multiplication gate would contribute a monomial of degree at least three to the output. Addition and multiplication with positive coefficients cannot remove it. Therefore every productive path contains at most one multiplication gate. Interpreting addition/multiplication as OR/AND produces a single-level Boolean circuit, contradicting the repository's 27 bound.

Consequently a 26-gate witness must have at least one target edge whose squarefree degree-two monomial is absent from its formal output polynomial. Every syntactic trace accepting that edge must repeat at least one endpoint. This offers a necessary condition for SAT or local search, beyond simply requiring a nested AND. Constants, unary gates, and invalid references must first be simplified correctly if this observation is used as a formal constraint.

For a constant-free binary network, its formal degree-one variable set and degree-two monomial set can be propagated cheaply. An OR unions both components. An AND has empty degree-one component and obtains degree two by multiplying the degree-one components of its operands. The output must omit at least one of the 21 squarefree edge monomials. This computation is not the same as evaluating the Boolean circuit on edge assignments, where repeated variables collapse.

## The unresolved gate accounting

A dirty rectangle can be filtered into legal edges. For example,

`((a OR b) AND (c OR d)) AND (a OR c)`

equals

`(a AND (c OR d)) OR (b AND c)`.

As isolated expressions the left side costs five gates and the right side four. This does not prove a global normalization: an operand or intermediate dirty rectangle may have multiple consumers, and a local replacement can discard useful shared work or duplicate its cost elsewhere. In a general circuit, operands can already contain legal edge terms as well as singleton terms, which a raw rectangle analysis does not account for.

The team's filtered-rectangle lemma controls an edge cover by one row and one column. To obtain 27, one still needs a global charging or transformation argument preserving total gate count and handling prior edge contributions and fanout. None of the reviewed results supplies that missing argument for Heawood. The generic single-level conjecture is false, so a valid proof would have to exploit the specific C4-free bipartite geometry or additional finite structural analysis.

## Search scope and limits

Searches covered quadratic monotone circuit normalization, C4-free and bipartite graph functions, single-level circuit bounds, graph representation, and read-1/multilinear arithmetic correspondence. I also read the primary ECCC landing page for [On Graph Complexity](https://eccc.weizmann.ac.il/report/2004/005/); its representation model does not settle exact Heawood computation. The Amano–Maruoka publisher abstract was found, but the full paper was not accessible through the attempted DOI redirect; no precise theorem from that unread full text is used here.

No claim that the posted statement is false is justified by this review. No claim that a 26-gate witness exists is justified either.
