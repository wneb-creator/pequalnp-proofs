L-meta-2583 lower-bound exploration

The statement asks for READ-1 per prime implicant: each incident point-line pair must have one proof tree reading both variables at most once. It does not require syntactic input fanout one.

Using L_meta_7684's point-star construction and L_meta_7639's matching lower bound, the target is equivalent to the sharp unrestricted monotone AO2 lower bound N*(q+2)-1. The incidence count is E=N*(q+1), and a point-star circuit has N AND gates and E-1 OR gates. For q=2, a26-gate monotone circuit for the Fano incidence function would refute the target because every READ-1 circuit needs27 gates. The prior PR13723 source already contains this equivalence and a weaker3N-1 unrestricted lower bound; copying those is not new progress.

Checked reusable normalization and block results reported by status_check:

- L_meta_4293: Lift preserves size, AO2, and function.
- L_meta_4295: a Lift fixed point exists.
- L_meta_7372: extraction into a core D with every gate not below the final graph function, plus operand pairs B whose ANDs cover the function, with D.size+2*B.length<=C.size+1.
- L_meta_7649: sharp star-cover cost if every non-below-output gate is OR with non-below-output inputs.
- L_meta_3760: any least AO circuit for a bipartite C4-free graph has junk-count different from1. This is a substantial10039-line checked theorem, not an easy one-step deletion.
- L_meta_4767 / L_meta_8149: sharp E+cover bound if every AND is below the output or accepts at most one true undirected edge-pair. This permits junk gates, but not a junk gate productive on multiple edges.

Consequently an obstruction to the sharp bound must contain at least two junk AND gates, one of which accepts at least two true edges. No proof has been found that the plane assumptions forbid this configuration or make it more expensive than a star cover.

OR-count strategy: it would suffice to prove at least E-1 OR gates, together with the existing AND lower bound N. Fixing exactly one point p true reduces the target to an OR of q+1 line inputs. A useful elementary fact is that if two monotone functions have an AND below a pure OR, at least one operand is below that OR: otherwise union two counterexample assignments, both still avoiding the OR's variables. This allows OR-only pruning for each point restriction, showing q OR gates are needed separately for each p. The unresolved part is proving the charges are disjoint across points and then charging the N-1 aggregation gates. The same shared core gate can behave differently under different point restrictions; no valid disjointness proof is available.

Warnings against shortcuts:

- L_meta_599 gives OR-count>=E-1 only under the stronger pseudoforest sparsity hypothesis (every induced vertex set has at most as many edges as vertices), which a projective plane does not satisfy.
- L_meta_2969 and L_meta_3444 refute naive additive core-block cost formulas even in lift-fixed bipartite C4-free circuits. Their witnesses are nonminimal, so they do not refute a minimal-circuit charging theorem. L3444 is live but has8 gates for a4-edge path with a5-gate star construction.
- L_meta_4849 refutes a universal no-garbage normal form for minimal triangle/C4-free graph circuits. Its graph contains the odd5-cycle0-4-7-1-6-0, so it is NOT a counterexample to the bipartite specialization. Its11-gate witness has4 AND and7 OR gates for8 edges, still exactly E-1 ORs.

Small rectangle example: a three-edge bipartite path can be written as (x OR x') AND (y OR y') AND (x OR y), eliminating the missing cross pair. This uses3 OR plus2 AND gates, versus a4-gate star construction. It illustrates how a junk rectangle needs a correction gate, but does not prove a general lower bound for multiple shared junk cores.

No complete proof or counterexample has been obtained in this exploration. No new Lean helper for2583 has been compiled by lower_bound yet.

Root identified stronger minimality machinery: L2668's internal lost_edge lemma says every gate of a minimal monotone circuit is pivotal on some true edge-pair, not merely present in the output cone. The L3444/L2969 block witnesses fail this property. For an OR gate, one can further reason that bypassing it by either child only decreases the output, so minimality gives a true edge-pair lost under each bypass. These two edge witnesses must be distinct. This establishes that every OR performs a genuine edge merge, but a proof that the merges give at least E-1 distinct charges remains missing; witnesses may overlap and downstream AND gates can filter their effects.

Small computational check (ordinary Python, not a Lean theorem): the Fano incidence graph defined by nonzero3-bit points/lines with zero dot product has21 edges and37 maximal independent sets, with sizes4(21 sets),5(14 sets),7(2 sets). Thus a simple CNF construction has37 prime clauses and is not an obvious route to an OR-count counterexample below20.

Further minimum-case exclusions from the source census: L_meta_5412 rules out exactly two independent double-star junk gates in a least lift-fixed bipartite C4-free circuit, under explicit neighborhood conditions on both rectangles. No unrestricted two-junk elimination was found. No checked minimal bipartite C4-free nonread1 witness was found either: L_meta_3679's general bipartite flattening counterexample contains C4s.

A top block need not equal the edge function of its accepted edge-pairs. It may also accept larger input sets that contain other graph edges. Replacing all top blocks by their accepted-edge DNFs would preserve the overall graph function: all true edges remain accepted and all newly accepted supersets are true graph inputs. However, showing that these replacements fit the existing gate budget is exactly the unresolved block-cost theorem. Simple AND reassociation is insufficient: the three-clause path example has no pair of its clauses whose conjunction is below the target.

A possibly more flexible target than OR-count>=E-1 is a tradeoff: if shared per-point OR charges save s OR gates, then at least s additional AND gates beyond N are required. This would yield the needed total cost even if the separate OR lower bound fails. No rigorous potential or charging invariant establishing this tradeoff has been found.

The proposed relaxation to vectors of one-hot point restrictions is insufficient: see onehot-obstruction.md for an explicit dual-rail arithmetic construction over the projective plane of order4096. It has at most2606N-73 binary monotone gates, computes every one-hot point row correctly for arbitrary line inputs, and is false on allzero point inputs, while the desired lower bound is4098N-1. The model loses necessary constraints from multiple true points. This is a theoretical construction, not Lean checked and not a counterexample to the actual gap.

Fanout-surplus strategy: in a live binary circuit with2N essential inputs andm gates, sum(outdegree-1) over nonoutput wires equals m-2N+1, the cycle rank of its underlying connected undirected dependency graph. The target sharp lower bound asks for surplus at leastqN. A canonical star circuit puts all this surplus on one input side. A possible reformulation is extraction of the incidence graph plus an output apex joined to a minimum vertex cover as a minor of the circuit dependency graph; this augmented graph has cycle rank E+N-2N=qN. No such minor-extraction theorem has been proved, and repeated-variable proof paths obstruct the obvious construction.

First-reader caution: if a point v is used exactly once, through AND(v,g), then g must be true on every neighboring-line singleton. It may also be true on extra singleton lines, with a later context filtering those extras. Under the one-hot restriction pure-OR meet-primality says one of those pieces already computes the exact neighborhood OR, but applying those choices independently across points is invalid, as the explicit relaxation counterexample demonstrates. Any weighted edge/fanout charge must control larger independent input sets, not only true and false point-line pairs.
