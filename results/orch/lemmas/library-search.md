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

### Review and restriction update
- Independently approved P4 counterexample audit SHA9635b2d227b31ef7d7e8ce8aab96a83d274a94834a97f07751df032bcdbe41d3 as partial preservation only. It satisfies all posted hypotheses but has one singleton-empty-support gate against cover number2, disproving that intermediate accounting lemma, not L-meta-4970.
- Independently approved semantic zero-cut snapshot SHA95cdc92511a5e56d38f529c62ee4fbf4f116d46b6298b1565f0fff4b9af47026: semantic pure-OR witnesses survive replacing a singleton-false gate by OR[]. Result deliberately does not assert AO2 for the intermediate zero gate.
- Found shortest TopForm normalization implementation L_meta_5779 (852 lines): pushOr_step574ff and main_aux817ff. All gate values on F=false inputs survive the rewrite, useful for multioutput pure-OR witnesses.
- Found all-wire zero compression L_meta_5138 build222ff, Option Nat map (none=false), ≤p−|Del|−|R|+sumL gates, exact binary AO gates. Setting Del singleton,Rempty,Lempty gives one gate saving while preserving all modified-wire functions.
- Read Jukna full paper https://web.vu.lt/mif/s.jukna/ftp/single1.pdf on 2026-11-25: no arbitrary bipartite/C4free AND-count=cover result found. Lemma3.12 and K2,2-free bound cited after it concern single-level circuits.
- Authored restriction partial review-extra.lean: outsideS inputs mapped to one appended-before-gates AND[] true; all wire values preserved; ORcount unchanged by shift. or_restriction_bound gives |S|−1≤ORcount when that restriction computes OR(S). Root independently reviews own-authored append.

### T0-preserving typed compression
Authored `TypedCompression` in results/orch/lemmas/review-typed.lean. A label for each new wire overapproximates its actual OR-reached inputs. Input labels are singletons; every OR reader has labels contained in its output label, and each OR output label is monochromatic. `labels_orIn` and `labels_tCount` prove this certificate implies T0. The zero compiler emits AND with empty labels and OR with original-gate OR-reach labels, preserving map-label inclusion while eliminating zero gates. `typed_build` preserves every modified-wire function, saves every explicitly deleted gate, and bounds new AND count by nondeleted original AND count. `typed_join_optional` adds at most one OR, preserving T0 when both operand labels lie in one monochromatic set, preserving AND count exactly.
Compiled snapshot review-typed-join-checked.lean SHA0fdb9597c491368b53ac7fa08825b30807ca9ff7f7ebb6602b479c0e8e0afd1f, build9 exit0; full log /tmp/oec/pequalnp-pilot-152/review-typed-build-9.txt. Root reviews authored module independently. Concrete cut-lift integration assigned semantic_proof, strict AND-count decrease assigned and_lower_bound.

### OR-reader bypass complement
Compiled `TypedCompression.Bypass.delGate_tCount`: L5779 ordinary gate deletion and wire rerouting preserve T0 when the replacement wire OR-reach is contained in that of the deleted gate. Uses labels `old.orIn(origWire newWire)`; equal-source cases preserve labels, the alias case uses the stated inclusion. Copied standard deletion syntax/AO helpers exactly from L5779. Also compiled `original_labels` and `append_or_tCount`, allowing one final OR whenever both operand reaches fit one monochromatic set. For lifting an earlier AND, its reach is empty, so only the output reach determines the set. Frozen review-typed-bypass-join-checked.lean2099lines SHA0577aa10fdee57cae7cd796708b24e9eb5f07ecc278e611d9ba89a4af743baa1; build12exit0. and_lower_bound agent handles semantic witness preservation and AND-index sum decrease.

### Independent OR-bypass review
Approved or-bypass-core-checked.lean720lines SHA4c021886a7535e29e973793c314beff010de47afad495d860bb9ec9abd75bec8, then full combined or-bypass-full-checked.lean3084lines SHAa9f48bee89918bb4008642d72e4d27eefbb499ec3a71e7b86f2bf8f4ed546250 and component906lines SHA3977767d055f64e3f2579a8add7660fca602672b9224e698d8b2aac8b260f48b. Reviewed new semantic decrease direction, pure-OR singleton preservation, exact final output restoration, unchanged AND-count bijection, strict AND-index sum using a later AND, actual OR-operand selection, and T0 via retained ancestorAND having empty OR-reach. Verified tail and component embedded exactly in compiled full source. These are partial rewrite lemmas, not the posted gate lower bound.

### Independent normalization and protected-frontier review
Approved semantic-minimal-no-reader-checked.lean2365lines SHA4aa11723e428632201d5447cd63fcd2e4af5c24bb99fed16c61a985b8aa4bcdb: lexicographic admissible minima preserve original output and pureOR functions; any directAND reader of a below-F AND would permit the checked cut-lift and strictly lower AND count. Output-validity is derived from all-true AO semantics.
Approved ledger-protected-component.lean SHA9126c4502ed641b267a59dbd15d3a3fb322e464d58f83d5e1f936171dbdb330f, checked assembly SHA3d84a11a20a83010c81d02d6ee3695a8c6d923006f41cdf500085d45cfeef27f: the forced-true protected wire must remain in a true frontier certificate because otherwise the unforced false circuit would be true. Its removal consumes the frontier +1, yielding inputcertificate size≤branchingAND count and strengthened global dirty-star bound |Q|≤#branchingAND. This is not an additive multistar budget.

2026-11-25T16:30:06.297720+00:00
### Research after full TopForm normalization
Read https://pequalnp.com/papers/note-1 on 2026-11-25. The page states exact edge-function bounds for forests, cycles, and sparse long-thread classes; it does not supply a general C4-free Boolean-circuit bound. Its Lean table is authoritative only for those explicit hypotheses. The useful several-output OR-family lower bound is already adapted in Semantic.

Existing checked residual ledger: L_meta_4183 final2499 (also L_meta_5781 final2513) gives |E|+T+2C+J+R <= size+U+1, with T=card(tops\centreless), C=card(centreless), J=card(junk), R=card(orN\lam), U=card(Ustar). It also yields a cover of the nonresidual star edges of size<=T. Thus a sufficient remaining lemma is a residual cover K with U+|K|<=2C+J+R. L_meta_8103 final2827 proves the combined full-cover version when J=1, via per-root pureBudget, mixing-target injection, and residual-lambda exclusion. L_meta_6240 proves 2U<=2C+J+R only under the extra hypothesis that every relevant gate accepts at most one residual edge. Neither additional condition follows from our posted hypotheses. R_meta_4185_7 explicitly leaves the general residual budget as a reduction hypothesis.

Leastness caveat: the master-ledger proof invokes S98.main_real to obtain |orT|+1=|tops|. Its star combinatorics otherwise use AO/F/C4. Our witness-preserving AND-minimal normal form is not globally IsLeastAO. A safe adaptation is to restrict tops to the output OR closure and use the already checked OR-closure bound; alternatively prove all tops occur there using admissible minimality. Never silently instantiate global leastness.

Potential semantic residual credit (mathematical argument, not yet Lean checked): use singleton-support crossproducts of boundary-top operands as semantic starEdges. A witness OR(Q) centered c and selected residual neighbors T subset Q should incur |T|-1 OR charges, each false at Zof(Q) and accepting two singleton probes in T. This follows by restricting the component-label invariant to T while retaining its original false baseline. Such charges are disjoint for distinct centers by C4. They also avoid semantic lambda (OR gates in a top leaf cone whose opposite operand accepts a singleton center d): both accepted singleton probes are adjacent d, hence d=c; both edges would then be semantic starEdges, contradicting residuality. Unlike a blanket charge-disjointness assertion, this uses two specifically residual probes. Still missing: one extra credit per residual witness component plus a residual cover; generic protected cofactor certificates are global and cannot yet be summed. No full theorem or counterexample has resulted.
