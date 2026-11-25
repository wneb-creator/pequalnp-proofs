# NOT elimination research for L-meta-9811

Research date: 2026-11-25 UTC. Read-only repository and primary-source search;
no change to the proof file. No applicable size-preserving normalization theorem
for arbitrary AND/OR/NOT circuits of bipartite C4-free quadratic graph functions
was found. This is a search result, not a claim that no such theorem exists.

The target has 14 variables and 19 edges. Its graph is cyclic and has vertices
of degree 3, so forest and cycle theorems do not cover it.

## Existing repository results

- `lean/PEqualNP/Outside/L_meta_287.lean:8236`: a minimal circuit for a forest
  graph function, optionally with isolated singleton terms, contains no NOT
  gates. The theorem explicitly assumes `G.IsAcyclic`.
- `lean/PEqualNP/Outside/L_meta_314.lean:7936`: minimal circuits for a single
  cycle of length at least 5 contain no NOT gates, with detailed wire-function
  classification. The adjacency is explicitly cyclic successor modulo n.
- `lean/PEqualNP/Outside/L_meta_173.lean`: connected acyclic graphs with an
  independent unique minimum vertex cover; again not the target graph.
- `lean/PEqualNP/Outside/L_meta_8692.lean:2393`: size-preserving monotone
  realization of one specific 5-input truth table, 0xeee0e880. Nearby finite
  truth-table normalizations do not give an arbitrary-graph theorem.
- `lean/PEqualNP/Outside/L_meta_4105.lean:502`: normalizes source lists of a
  minimal circuit, retaining a valid one-input NOT or a two-input AND/OR at
  each gate. It does not eliminate NOT.
- `lean/PEqualNP/Outside/L_meta_217.lean:7350`: C4-free graphs and vertex-cover
  lower bounds at most 5 imply a lower bound on AND gates, but `Monotone2 C`
  is already a hypothesis.
- `lean/PEqualNP/Outside/L_meta_8933.lean:1469`: the strong graph-size bound
  uses `TopForm.IsAO2` and an additional junk-AND exclusion hypothesis.
- `R_meta_1031_1.lean` and `R_meta_972_5.lean` also concern monotone/top-form
  circuits; they do not bridge arbitrary circuits to monotone circuits.

Search artifacts in this scratch directory: `normalization-files.txt`,
`normalization-matches.txt`, `c4-matches.txt`, `c4-circuit-matches.txt`,
`c4-theorem-statements.txt`, `normalization-specific.txt`, and
`normalization-statements.txt`.

## Exact conditional theorem from primary literature

Stasys Jukna, *Notes on Boolean Read-k and Multilinear Circuits*, ECCC TR22-094,
revision 2, 26 December 2022, Section 6, Definition 2, Theorem 3, Corollary 1.
Read on 2026-11-25:
https://eccc.weizmann.ac.il/report/2022/094/revision/2/download/

Theorem 3 gives a size-preserving monotone simulation of a semantically
multilinear DeMorgan circuit for the upward closure of its output function.
Corollary 1 gives equality of monotone and nonmonotone multilinear complexity
for monotone functions. Semantic multilinearity means the two functions at
every AND gate depend on disjoint sets of variables. DeMorgan form permits
negations only on input variables. Page 10 explicitly records that converting
arbitrary internal-NOT circuits to this form may double the size. Thus two
missing conditions remain: no-overhead DeMorgan conversion, and multilinearity
of the resulting circuit. A homogeneous quadratic output is not a stated
substitute for either condition.

Section 6.2, Fact 6 gives a sharper diagnostic: replacing every negative input
literal by 1 computes the upward closure exactly when every contradictory
term produced syntactically has a positive factor already implying that
closure. Non-cancellation suffices. Neither C4-freeness nor bipartiteness is
shown there to force this circuit condition.

## Other primary results and why they do not close the gap

Paul E. Dunne, *Ceilings of Monotone Boolean Functions*, Theorem 3.1.
Read on 2026-11-25:
https://web.vu.lt/mif/s.jukna/boolean/Dunne-ceilings.pdf

For a suitable ceiling h of g, the monotone complexity of
F = (f AND g) OR h is at most 6 times its unrestricted complexity plus n times
the monotone complexity of h. This is an overhead simulation. It does not
preserve the exact 24-gate budget. The proof uses monotone substitutes for
negative literals between the two restrictions F[x_i=0] and F[x_i=1]. Their
construction costs gates and is not automatically available for free here.

Stasys Jukna, *On Graph Complexity*, ECCC TR04-005 revision 1, Definition 1.1,
Section 7 and Theorem 7.3. Read on 2026-11-25:
https://eccc.weizmann.ac.il/report/2004/005/revision/1/download/

Graph representation in this paper constrains only assignments containing
one selected vertex from each side (or two selected vertices in the ordinary
graph model). This is weaker than computing the exact graph function on every
assignment. Theorem 7.3 supplies monotone depth and formula-length bounds for
triangle-free C4-free graphs, not a general-circuit gate count. Magnification
therefore does not remove NOT gates at the exact target budget.

Stasys Jukna, author abstract for *Disproving the Single Level Conjecture*.
Read on 2026-11-25:
https://web.vu.lt/mif/s.jukna/papers/single.html

This compares single-level monotone circuits with arbitrary monotone circuits
for quadratic functions. It does not compare unrestricted circuits with
monotone circuits. The PDF itself timed out twice. Any stronger theorem from
the PDF's search snippets remains UNVERIFIED because the PDF was not read.

## Consequence for the proof effort

A graph-specific argument excluding useful cancellations, or a no-overhead
normalization to semantically multilinear DeMorgan form, would be new work in
this search. Importing a monotone lower bound alone is insufficient. A finite
exact circuit exclusion remains logically sound as an alternative, provided
its enumeration/normalization and UNSAT certificate are checked in Lean.
