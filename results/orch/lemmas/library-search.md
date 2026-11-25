# L-meta-4970 library search

Only existing Outside file containing the actual identifier `tCount` or `TwoColour` is
`lean/PEqualNP/Outside/L_meta_4791.lean` (1414 lines). It constructs a circuit with T=0
at a bounded size increase; it is not a lower bound and cannot solve the goal directly.

Useful self-contained OR reach toolkit in L_meta_4791:
- orReaches_iff line 626; self 646; step 650; bound 656; trans 670.
- mem_orIn 708; orIn_self 716; orIn_up 719; orIn_reach 728; orIn_val 737.
The last lemma proves any true input in orIn forces the wire value true. Helpers only
need library/Defs dependencies, but unlisted Outside modules cannot be imported: adapt
needed source into the final file's own namespace.

Other generic helpers: MetaComplexity/Helpers/LowerPart.lean (443 lines) has
IsAO2 operand bounds, wire evaluations, monotonicity, OrReaches recursion and bound.
LowerPart2.lean (248 lines) has reach_self (74), reach_trans (77), truth propagation.
These later specialize to OneDirty and are not by themselves a global gate lower bound.

R_meta_2714_2.lean is an existing reduction for a related normal-form refutation. Its
hypotheses decompose a star-cover ledger: a forest bound |union leaves| ≤ roots+branches,
a center cover count, and gate budget 2*roots+branches ≤ size+1. It does not prove any
of these hard hypotheses, so cannot be used as a finished lower bound.

L_meta_3140.lean (1700+ lines) includes substantial constant propagation and a starBuild
construction, but solves a local gate elimination statement with many additional
hypotheses. No directly applicable stronger theorem found so far.

## Partial preservation review

2026-11-25T15:43:02.227627+00:00: Reviewed the 15-line L_meta_4970.lean empty_edges lemma. APPROVED FOR
PARTIAL PRESERVATION ONLY after compilation: S=empty yields vacuous cover and 0≤size+1.
Allowed import and own namespace, no forbidden text/options/attributes/axioms found.
This file lacks the posted final theorem and is not eligible for a proof PR/checker claim.

## Further lower-bound precedents

- L_meta_4897 (1961 lines): target bipartite cover bound with extra IsReadK(...,1).
- L_meta_2235 (1770 lines): cover bound for only the edges with readsAtMost pair=1.
- L_meta_2237: graph version of read-once target.
- L_meta_8933 (1476 lines): target graph bound when no dirty AND is true on two distinct
  edges that both fail readsAtMost1. These hypotheses are not immediate from ours.

Useful machinery to adapt (all unlisted modules, so copy source not imports):
- L_meta_8933 singletonSupport definition255, births283, positiveInputs298, merges307.
- gate_budget323–415: 2*births.card+merges.card ≤ size+1, using empty-support reachable
  wires/readers count. Requires all reachable AND outputs have empty singletonSupport.
- leaf_budget431–527: multi-root singleton-support OR count with star adjacency constraints.
- birth_route574–646 and birth_star648–690 route edges through clean ANDs.
- graph_budget697 onward gets final cover, but assumes every reachable AND true at a pair
  implies graph adjacency (hsafe). Cannot use without additional proof/normalization.
- L_meta_2235 s2233 at817–1025: for arbitrary AND set F in OUTPUT OR closure,
  |F| ≤ #output OR+1. Its statement is at977.
- L_meta_2235 s2234 at1026–1558: disjoint leaf-OR accounting for stars, including
  orIn union recursion and forest leaf bounds. The statement is at1550.

Structural caution: T=0 constrains syntactic orIn, not semantic singleton support.
The circuit (a AND a) OR (b AND b) has mixed singletonSupport but no syntactic
OR-reachable inputs, hence T=0. Positive/duplicating AND gates need explicit accounting.
The final hypothesis only says pure star OR values exist somewhere; they can be dangling
and need not feed the output. Do not assume output provenance from those witnesses.

Partial stars.lean reviewed independently: all five helpers are valid graph/finite-set
facts, same own namespace and allowed import, no forbidden proof facilities. Approved
for partial preservation after the reported compilation, not a full proof PR.

## Semantic OR cost precedent and reviews

L_meta_1458/1377 charge semantic OR gates, with arbitrary intervening ANDs:
charged243, frontier351–440, charged_count499–518, apart_counts520–584. For pure
OR output S and R=empty, choose outside-S assignment, trace false AND via one false
child, OR via both. This proves |S|-1 charges, disjoint across intersection≤1 families.
Semantic agent independently adapted shorter L_meta_529 into semantic.lean (341 lines).

2026-11-25T15:46:33.453922+00:00: Independently reviewed full semantic.lean, revised stars.lean,
ledger.lean, and counterexample.lean. APPROVED FOR PARTIAL PRESERVATION after their
reported successful compilation. No full gap theorem claimed. Semantic invariant and
OR-only charge proof are sound; graph helpers use exact C4-freeness; ledger distinguishes
syntactic from semantic support; auditC uses kernel decide to demonstrate empty orIn at
pure-OR output. For final file prefer helper lemma declarations rather than theorem.
