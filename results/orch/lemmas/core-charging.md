# L-meta-2962 charging route

## Algebraic target

Let D be the union of accepted edge sets of maximal cores and U the union of their cones. A sufficient stronger inequality is |D| + tau(D) <= |U| + mc, since a cover of G-D together with a cover of D covers G. Structural agent is handling cover algebra.

Alternative sufficient inequality: for any fixed maximum matching M of the bipartite graph G, |D| + |M intersect D| <= |U| + mc. The residual graph contains M-D, so tau(G)-tau(G-D) <= |M intersect D|. This needs matching/cover equivalence, likely heavier than a direct cover certificate.

## Main obstruction

Summing one-core bounds overcounts shared gates. A proof must charge overlap against repeated edges or saved cover vertices, or choose an ordering where each newly added core pays its newly added edge/cover contribution from newly exposed gates. No available checked theorem handles this overlap directly. Such an incremental assertion is not yet verified.

The lift-fixed condition constrains only live gates. Dead maximal cores can have arbitrary internal lift sites, so arguments cannot apply fixed-point normalization separately inside every core.

## Useful finite example

Counterexample agent found a tight one-core path example: e=d AND b; s=b OR c; t=a OR e; root=t AND s. It accepts exactly edges ab, ac, bd and has |D|=3, tau(D)=2, |U|=4, mc=1. The root rereads b on edge bd. The internal OR lift site is permitted if this core is dead and the circuit has an independent exact output. Thus no margin stronger than the stated bound is available uniformly.

## Nearby checked counterexamples

L_meta_2969 refutes the companion outside-core count. L_meta_3444 refutes its private-cone correction. L_meta_3446 refutes the private-cone version of the core-cover bound. Full cone cardinality in our statement is essential.

## Primary source checked

Read 2026-11-25: Stasys Jukna, Disproving the Single Level Conjecture, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, section3.5. The K2,2-free |E| lower bound stated there applies to single-level monotone circuits; it uses limited sharing of OR sums. The paper does not supply our general circuit bound. Its separating examples use saturated, nonbipartite extensions, so do not directly refute this task.

## Lean partial

CoreStructure.lean contains reused wire-evaluation helpers from L_meta_3653 and new core_op_and / maximal_core_op_and lemmas. They use only the AO2 model and graph simplicity, no lift or no-four-cycle hypotheses. Compile passed (exit 0, warnings only); full output in /tmp/oec/pequalnp-pilot-71/lemma-search/core-structure-build.log.


## Strong obstruction: the posted statement already implies an edge-count lower bound

This is a mathematical reduction sketch, not yet formalized in Lean. Let H be any nonempty bipartite C4-free graph, and let A be an arbitrary AO2 circuit computing its exact edge function F. Prune unused gates; write m for its size. Let T be a minimum vertex cover of cardinality t >= 1.

1. Append a binary OR tree z on the inputs in T, costing t-1 gates (or use its sole input when t=1).
2. Append r = F AND z, costing one gate. Because T covers H, r still computes F.
3. r is a core: its F operand is implicant and its z operand is not (z accepts a singleton); every proof tree on an accepted edge includes both endpoints through F, then one endpoint of T through z, so at least one endpoint is reread.
4. Every old gate lies in r's cone after pruning. Hence r is the only maximal core in this component. Its gamma edge set is E(H), and its cone has m+t gates.
5. Make this entire component dead and append a separate canonical star-cover circuit for F as the actual output. The canonical component is lift-fixed and contains no cores: each accepted edge has a read-once proof. This makes the combined circuit satisfy the posted lift-fixed hypothesis, because dead lift sites are ignored.
6. Thus the combined circuit has D=E(H), U of size m+t, mc=1, and the residual graph has empty minimum cover. The target inequality reduces to |E(H)|+t <= m+t+1, or m >= |E(H)|-1.

For projective-plane incidence graphs, this entails a superlinear lower bound in the number of inputs. This deduction explains why a straightforward cone-sharing argument would be unexpectedly strong; the lift-fixed hypothesis cannot make the dead-core case easier.

## Literature check supporting the obstruction

Read 2026-11-25: Jukna, SIAM Journal on Computing 36(1) (2006), author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf, section8 (PDF page17), Problem8.2 explicitly asks for a superlinear monotone-circuit lower bound for an explicit quadratic Boolean function. The discussion distinguishes known superlinear formula bounds from the unrestricted circuit problem. Section3.5's K2,2-free edge bound is only for single-level circuits.

The 2005 primary preprint https://eccc.weizmann.ac.il/report/2005/021/download/ says the same in Problem24 and immediately preceding discussion of explicit K2,2-free bipartite graphs. This is a historical status check. Current2026 status is UNVERIFIED: targeted searches did not find an authoritative recent resolution or survey confirming that the problem remains open. No claim that the posted statement is false follows from this obstruction.


Independent mathematical sanity check: agent single_core reviewed the dead-wrapper reduction and found it sound for nonempty H, contingent on formalizing pruning and the ReadK proof-tree semantics. In particular, the canonical live output adds no core, while every old core lies below the new root. No Lean verification of the whole reduction is claimed.

The obstruction already uses one maximal core: arbitrary DAG sharing remains inside its cone. Disjointness between different maximal core cones does not permit replacing a circuit by a formula without charging duplicated shared gates.

## Separate AND-count route (research, not proved)

Parent proposes the two inequalities |D| <= OR(U)+mc and tau(G)-tau(G-D) <= AND(U). For the second, a sufficient stronger theorem would be: if a monotone circuit output h is below the edge function of a bipartite C4-free graph, and D is the graph of accepted pairs of h, then tau(D) <= its number of AND gates. OR-combining all core outputs introduces no AND gates, and covers of D and G-D combine. Alternatively, an exact-graph AND lower bound tau(G) <= AND(C) suffices after adding a canonical star circuit for the residual graph. Neither stronger theorem has been established.

The first-creation charging rule is insufficient: (a OR b) AND (c OR d), subsequently AND (a OR c), computes the P4 graph with edges ac,ad,bc. All three edges are first created at the first AND, but two vertices are required to cover them. A successful proof must charge the later filtering AND even though it first creates no edge.

Primary sources read 2026-11-25:

- Ingo Wegener, The Complexity of Boolean Functions (1987), https://web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf, section6.8 and exercise6.18: exact AND counts for Boolean matrix product and disjoint bilinear forms use special replacement rules. These hypotheses do not hold for arbitrary single-output bipartite C4-free graph functions. No generic bilinear normalization follows from this source.
- Andrzej Lingas and Mia Persson, Improved Lower Bounds for Monotone q-Multilinear Boolean Circuits (2023), https://arxiv.org/pdf/2305.07364, introduction and Theorem4: the stated AND lower bound applies to read-once/multilinear semi-disjoint bilinear forms. A general circuit may reread variables, precisely the issue here.
- Teofilo Gonzalez and Joseph Ja'Ja', On the Complexity of Computing Bilinear Forms with {0,1} Constants (1980), https://sites.cs.ucsb.edu/~teo/papers/JCSS-BForm.pdf: the model explicitly restricts each nonscalar product to an x-linear times a y-linear form over integers. Its graph decomposition characterization cannot be imported into unrestricted Boolean circuits.

No authoritative primary source found proves or refutes the unrestricted AND-count claim. Its current status remains UNVERIFIED; failure to find a theorem is not evidence of falsity.


## New checked AND charge

CoreAndCharge.lean compiled successfully (exit 0; warnings only), with full output preserved in CoreAndCharge.validation.txt. It copies the vector and cone infrastructure from LeafUnionStrict.lean through section Vectors, plus CoreStructure.lean, then adds:

- pure_or_witness: an accepted pair at a wire with an OR-only cone supplies a singleton witness together with its unit read-vector.
- core_has_and_ancestor: every core has a distinct AND ancestor in its cone. Otherwise both root operands are OR-only; their singleton witnesses must differ because the root is below a graph function, giving read-vector [1,1] and contradicting ReadTwiceAt.
- core_two_and_gates: each core cone contains at least two AND gates.
- maximal_cores_and_charge: if maximalCores is nonempty, the union of its cones has at least mc+1 AND gates. Every maximal core root is an AND; an AND ancestor of any chosen root lies in the union but cannot itself be maximal.

These lemmas use AO2 and simple-graph semantics only, with no bipartite, no-four-cycle, or lift-fixed assumptions. They are structural partial results, not a proof of the posted full inequality.


Additional historical primary-source check (read 2026-11-25): Peter A. Bloniarz, MIT/LCS/TR-238 (1979), chapter3 and appendix1, https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TR-238.pdf (readable scan: https://bitsavers.trailing-edge.com/pdf/mit/lcs/tr/MIT-LCS-TR-0238.pdf). The appendix identifies biclique-cover number with vertex-cover number for graphs without 4-cycles, but chapter3 theorem3.13 connects that number to single-level AND complexity only. The unrestricted AND lower bound there is exhibited for disjoint unions of triangles. Thus this older source also does not establish the needed arbitrary-circuit cover inequality.


Stronger dead-wrapper observation (suggested by structural_proof, mathematically checked here, not Lean formalized): for any exact nonempty graph circuit A with output F and any input x, append q=F OR x and r=q AND F. This costs two gates. q is not implicant because it accepts singleton x, and r computes F. Every accepted-edge proof through r either uses F twice, or uses F plus an endpoint x; either way some endpoint is repeated. Thus r is a core containing the entire pruned A. Appending a separate canonical live output gives D=E, U=m+2, mc=1, so the posted target entails m>=|E|+tau(G)-3. This improves the earlier, more expensive OR-cover wrapper deduction. The missing formal work remains construction semantics, read-vector positivity, and canonical output padding.


Three-copy amplification removes the additive two-gate loss. For an arbitrary circuit A of size m computing a nonempty C4-free bipartite graph G, let H be three vertex-disjoint copies of G. Its edge count and minimum cover size are 3|E(G)| and 3tau(G). Three disjoint copies of A joined by two OR gates compute H with 3m+2 gates. Applying the two-gate dead-wrapper construction above gives a sole maximal core with U-cardinality 3m+4 and mc=1. The posted inequality therefore gives 3|E(G)|+3tau(G) <= 3m+5. Since all quantities are integers, m >= |E(G)|+tau(G)-1. Conversely, the core-cone compression plus canonical residual circuit construction described by counterexample gives the posted inequality from that global exact lower bound. This is an informal equivalence of mathematical statements; no formal construction, compression, or amplification theorem is claimed.


## Checked cyclic near-tight example

CyclicCore.lean compiled successfully (exit 0), with complete output in CyclicCore.validation.txt. This is a positive example, not a refutation. The graph on Fin6 has edges 03,05,13,14,24,25, forming C6. The nine-gate prefix computes this edge function, but its output is dead; an independent eight-gate canonical star-cover circuit computes the actual output. All posted hypotheses are checked. The sole maximal core is gate8; D has six edges, U has nine gates, the original minimum cover has size3, and the residual cover is empty. The posted inequality is 9<=10, exactly margin1. The example uses kernel decide only.


Independent informal-equivalence review: counterexample checked the wrapper, pruning requirement, singleton obstruction, canonical padding, three-copy cost accounting, cover additivity, and integer rounding. Their verdict is mathematically sound, with U<=m+2 sufficient after pruning; the converse compression argument handles the residual-empty case separately. This review supplies no Lean certification of the equivalence.


## Checked pair-vector soundness

ReadVectorSupport.lean compiled successfully (exit 0), with full output in ReadVectorSupport.validation.txt. It copies StrictLeaf through Vectors and adds pair_vec_shape, pair_vec_sound, pair_vec_zero_left, pair_vec_zero_right, graph_unit_false, and below_pair_vec_pos. A cap-1 ReadK vector on [u,v] always has two entries. If all variables named by positive entries are true, the wire is true. In particular, a zero u-coordinate makes the wire true on singleton v, and vice versa. Therefore a wire below a simple graph edge function has both entries strictly positive in every such vector. These lemmas do not require bipartiteness, no-four-cycle, exact output correctness, or a lift fixed point. They provide the semantic ingredient for the generic repeated-output wrapper proof.


### Final obstruction assessment: arbitrary circuits versus bilinear normal form

The most promising unproved route remains two separate charges:
`|D| <= OR(U) + mc` and `tau(D) <= AND(U)`.
The second would imply the required cover drop, since a minimum cover of D together
with one of G-D covers G. It is stronger than the exact requested cover-drop bound.
Computational searches support both charges, but there is no general proof here.

A precise obstruction to importing a bilinear-arithmetic or first-AND argument is
already the four-vertex path with edges ac, ad, bc. The circuit
`((a OR b) AND (c OR d)) AND (a OR c)` computes exactly that graph function.
The first AND creates all four cross pairs, including the nonedge bd. The final AND
removes bd while retaining ac, ad and bc. Both matching edges ad and bc have the
same first mixing AND and the same final mixing AND, so choosing either a first
or a last gate does not give a matching-to-AND injection. A Hall argument must use
multiple available gates and account for the filtering obligation.

The arithmetic polynomial obtained by replacing OR by addition and AND by
multiplication is `(a+b)(c+d)(a+c)`, homogeneous of degree three. Its degree-two
part is zero. Its Boolean squarefree reduction has minimal degree-two monomials
ac, ad and bc, arising from repeated-variable degree-three monomials. Thus the
usual degree-two homogeneous extraction deletes the whole useful computation.
The graph is bipartite and C4-free, so those hypotheses do not fix the problem.
A normalization theorem must explicitly handle Boolean idempotence and prove
that the number of AND gates does not increase; that theorem is exactly the
missing substantive step, not an available algebraic simplification.

The checked wrapper theorem now makes the issue formal at the core level:
`AbsorbWrapper.isCore` says that appending `(F OR z) AND F` to ANY exact nonempty
graph circuit creates a core, assuming only AO2 and a valid old output. Its
proof uses `wrapper_readTwice`, which shows every pair proof repeats a variable.
No bipartiteness, C4 condition or normal-form assumption enters that theorem.
Together with the separately proved append/cone helpers, this confirms that the
posted maximal-core mechanism includes arbitrary graph-function computations;
it cannot by itself supply a missing homogeneous normal form. The full
three-copy equivalence argument above remains informal because generic disjoint
copying and canonical live-output padding have not yet been formalized.

Fresh standalone checks:
- WrapperReadTwice.lean: Lean exit 0, no diagnostics.
- AbsorbWrapperCore.lean: Lean exit 0, no diagnostics.
- Both final theorems use only propext, Classical.choice and Quot.sound in the
  axiom audit; no additional axiom or unsafe decision procedure.
