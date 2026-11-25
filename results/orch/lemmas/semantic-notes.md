# Semantic support route

A general binary circuit uses at least the number of essential variables minus one gates. Adapted the existing support invariant from Helpers/Support.lean into a local namespace with only PEqualNP.Defs imported; Lean-checked. This handles all star forests because their nonisolated vertex count equals |E|+tau. For a general C4-free graph with a cycle, essential support is too weak: on a six-cycle it yields 5 gates while the target is 8.

The gate-count invariant is joint support cardinality <= number of gates + number of selected wires. Removing a selected newest gate and adding its at-most-two children increases the selected-wire budget by at most one.

Next: show every edge endpoint is essential for the exact bipartite edge function and derive a Lean-checked star base case.

## Implemented special cases (Lean-checked)

- `essential_card_le`: any selected essential input set has cardinality <= number of gates + 1.
- `edge_endpoints_card_le`: both projections of E, embedded in Fin(p+l), form an essential set for the posted edge function.
- `point_star_bound`: if every edge has the same point endpoint, the exact target conclusion follows; no C4-free or T=0 assumptions needed.
- `matching_bound`: if both projections on E are injective, the exact target conclusion follows; again no C4-free or T=0 assumptions needed.

A potential strengthening is to express the deficit as fanout excess. In a connected binary circuit cone, gates+1 = number of input leaves + excess fanout. The remaining needed inequality is excess fanout >= |E|+tau-|V_active|. Pure shared OR regions reused by two distinct centers create a C4, but dirty AND filtering complicates charging. No valid general charging inequality obtained yet.

2026-11-25T17:16:33.443492+00:00: semantic-support.lean passed lake env lean with exit 0 and empty stdout/stderr. The complete target is proved for arbitrary point-stars and matchings as conditional special cases, not for arbitrary C4-free graphs.

## Further checked components

- semantic-linear.lean: `and_below_linear` and `or_below_linear` implement semantic pruning under a linear target. Both files now compile with no warnings after replacing the deprecated negation tactic. Source is frozen for parent push.
- semantic-starforest.lean: `star_forest_cover` proves that a bipartite graph in which every edge has a degree-one endpoint admits a vertex cover S with |E|+|S|=|V_active|. Orient each edge from its selected leaf to its center; leaf assignment is injective, and leaf and center images are disjoint. This combines immediately with `edge_endpoints_card_le` to establish the posted circuit conclusion for all star forests.
- Star-forest source compiled with exit 0 and only deprecation warnings for if_pos/if_neg. Source frozen without cosmetic changes.

The full problem remains beyond endpoint support: on a six-cycle, |V_active|=6 but |E|+tau=9. A strengthening needs to account for circuit fanout/graph structure, rather than adding more endpoint-essentiality lemmas.

Updated 2026-11-25T17:18:50.855993+00:00.

## Checked size/T0-preserving normalization

Latest self-contained file: `semantic-pairinactive.lean`. It supersedes the namespace bodies in semantic-fold.lean, semantic-fold-build.lean, semantic-fold-delete.lean, and semantic-delete-gate.lean; do not concatenate these duplicate supersets.

- `orIn_snoc_old`: appending a gate leaves every old wire's OR-reach unchanged.
- `build` / `fold_prog`: actual constant propagation through an acyclic AO program. False AND outputs disappear; ORs with one false operand bypass to the survivor. Surviving representatives have OR-reach contained in the supplied old reach sets, so monochromatic OR reach and T=0 are preserved. Result size is at most the retained-gate count. Uses only products, options, and existing types; no new structure declarations.
- `delete_gate`: if some positive input has gate j=false, remove gate j and propagate false. Returns strictly smaller AO2 T0 circuit D, pointwise D<=C, equal to C at every input where gate j=false.
- `delete_pair_inactive`: if gate j is false on every target edge pair, deletion preserves the entire graph edge function (via monotonicity and its minimal positive assignments).
- `normalise_pair_active`: least-size selection now gives an equivalent size-nonincreasing AO2 T0 circuit in which EVERY gate accepts some target edge pair.

All six named components above are Lean-checked in the latest file with exit0 and empty stdout/stderr. Remaining main gap: charging edge-active dirty gates; no claim that pair-active implies pair-clean.

Normalization completed 2026-11-25T17:30:05.259219+00:00.

Latest normalization superset is now `semantic-least-active.lean`, checked exit0 with empty logs. Its last lemma `least_pair_active` gives gate pairactivity for any FIXED constrained least-size circuit. This is the form needed to combine with library agent's top-form witness without applying a second normalization that might disturb top form. The library wrapper orders hmin assumptions AO, computes, T0; adapt by `fun D hAO hT hfun => hmin D hAO hfun hT`.

Further mathematical observation sent to structural agent: in a top-form circuit, the earliest dirty AND has no AND ancestor. Earlier ANDs are clean, and top form forbids clean AND ancestors of any AND. Thus its operand functions are pure ORs of their reach sets. If their colors agree, pairactivity forces those reach sets to intersect; an edge pair has only one true input of each color. Opposite colors yield a rectangle that contains some target edge, but may contain nonedges requiring later filtering.

Updated 2026-11-25T17:31:45.801170+00:00.

## Separate OR-count route and exact finite tests

T=0 alone cannot strengthen an OR-only lower bound: buffering both operands of every OR with idempotent AND gates preserves the Boolean function and OR count while making each OR's direct OR-reach empty. Thus proving OR_count >= |E|-1 in T=0 also proves the unrestricted monotone OR-count bound.

`semantic-orfree.py` exactly encodes circuits with k OR gates and arbitrarily many AND gates. Flatten every AND-only region into a conjunction of selected input variables and earlier OR outputs; every OR node has two such conjunction operands, and the output is one final conjunction. Nonempty conjunctions suffice in the no-constant model. Redundant/idempotent OR padding means exactly k nodes cover all circuits with at most k ORs. Commutative operand ordering loses no solutions.

C6 (six inputs, six edges): pinned known5-OR circuit is SAT and independently replays all64 truth-table rows. The k=4 test is UNSAT in0.25seconds, giving computational evidence for OR>=5 even with unbounded AND gates. This is not a Lean theorem. Counterexample agent independently reviewed the encoding and flattening argument and found it sound.

`semantic-orfree-fano.py` applies the same unrestricted-AND encoding to the Fano graph. Its20-OR star circuit passes pinned SMT validation and independent all16,384-input replay. The19-OR query uses all21 edge positives and37 maximal-independent negatives (a complete monotone semantic test set); its final result was UNKNOWN after300seconds, so it supplies no lower bound.


## 2026-11-25T17:48:39.177967+00:00 Contextual pivotality checked

`semantic-pivotal.lean` compiled successfully with empty stdout and stderr. It supersets semantic-least-active.lean and is frozen. Exact kill semantics are exposed as `cutProg`, `cutKeep`, and `cutFun`; `cut_solution_exists` and `cut_unique` show the interpretation exists and is unique. `fold_cut` builds a strictly smaller AO2/T0 circuit for any nonzero cut output. `least_gate_pivotal` shows every gate of a size-minimal AO2/T0 equivalent destroys some positive edge when forced false, stronger than mere edge activation.

The unrestricted-AND Fano 19-OR query timed out UNKNOWN at 300.2 seconds; this is not a lower bound. The pinned 20-OR construction passed full 16,384-row replay. The C6 4-OR query remains UNSAT (exact unbounded-AND encoding). Small C8 6-OR and C6-with-pendant 5-OR queries now run with 30-second caps after known (m-1)-OR constructions passed full-table replay.


## 2026-11-25T17:51:20.236565+00:00 No-unused and output-last checked

`semantic-no-unused.lean` compiled with empty logs, superseding semantic-pivotal.lean. `cut_same_of_no_reader` shows exact cut evaluation is unchanged when the forced gate has no readers and is not output. Contextual pivotality gives `least_no_unused`, with the exact later-reader signature needed by TreeCount.balance. `graph_output_ge` uses singleton falsity; `least_output_last` then gives n <= output and output+1=n+gateCount. All apply to the same constrained minimum witness.

The C6-with-pendant graph needs at least 6 OR gates even with unbounded ANDs, according to the exact SMT encoding: 5-OR query UNSAT in 3.831 seconds. C8 6-OR query UNKNOWN at its 30-second cap. These remain computational evidence only, not Lean proofs.


## 2026-11-25T18:03:07.169388+00:00 Generic OR-DAG raw cut and cross-centre obstruction

`semantic-rawcut-complete.lean` compiled with empty logs. It defines an explicit raw/payload input state and binary DAG fold, verifies the raw-cut support invariant, and proves `raw_cut_complete`: v <= r+m+t0 and (M-r-m)+(t-t0)+v <= M+t. This is a support/count certificate; an actual multioutput circuit transformation and application to the whole lambda network are not included.

`semantic-bank-obstruction.py` checks a 13-gate AO2/T0 circuit on all 128 inputs, computing the C4-free forest z1-{a,b,u}, z2-{a,c,v}. It is TopForm, every gate is contextual-edge-pivotal, and each OR branch is contextual-edge-essential. Its shared mixing wire a OR h, with h=(u OR z2) AND (v OR z1) AND (u OR v), feeds two lambda banks {a,b} and {a,c} at different centres. Per-centre counting would assign only one attachment gate after the pure banks are free, but the two distinct bank-OR-h outputs require two. Thus genuine minimum size is still needed beyond the proved necessary minimum properties. The circuit is nonminimum (13 versus a known 7) and is NOT a counterexample to the gap. Exact gates and complete validation appear in task-scratch semantic-bank-obstruction.json.


## 2026-11-25T18:10:59.173845+00:00 Genuine minimum masked-region cofactor checked

`semantic-masked-region.lean` compiled with exit0 and empty logs, superseding semantic-no-unused.lean. It exposes `maskSrc` and `maskProg`, setting raw input a=false only on direct reads inside a selected gate region R. Under the explicit conditions that output is outside R and every outside gate reading R is an OR with raw a as an operand, `mask_values_outside` proves exact equality at all outside gates for every input. `mask_region_smaller` folds the program into an AO2/T0 circuit and strictly decreases size if R has any direct a-read. `least_mask_region_no_read` rules out all such reads in any constrained minimum. No ancestor closure is required for the cofactor transformation itself.

The 13-gate obstruction is now kernel checked in semantic-bank-obstruction-scoped.lean, with resource options scoped directly to each lemma. The original unscoped checked file remains intact. Exact two-new-signals obstruction is kernel checked in semantic-bank-factor-impossible.lean. Both are regression results about invalid shortcuts, not refutations of L-meta-4675.


## 2026-11-25T18:12:27.801063+00:00 Mask-avoiding dirty witness checked

`semantic-masked-witness.lean` compiled with empty logs and supersets semantic-masked-region. `RegionClosed` is explicit closure under gate operands. `closed_region_ignores_input` proves that all gate functions in a closed region ignore raw a when no region gate reads it directly. `least_mask_dirty_witness` combines the no-read consequence of constrained minimum with that independence and monotonicity to produce a genuinely dirty input with a=false.

OR-path domination can be represented by enlarging a region along unmasked paths until direct a-ORs form its boundary. However domination of a payload output alone need not dominate other readers of shared ancestors. The cofactor theorem remains safe for any explicit full boundary, while its witness corollary needs ancestor closure; copying shared ancestors may cost gates and is not justified by the current result.


## 2026-11-25T18:25:11.783105+00:00 Aggregate trace charge and disagreement obstruction

`semantic-cluster-disagreement.lean` compiled successfully (one inherited deprecated dif_pos warning), superseding semantic-cluster-charge. It proves common-witness aggregate centre charging without counting shared paid ancestors twice. For distinct witnesses, it defines jointSupport and necessary disagreement gates: an unpaid node is charged only when its aggregate support fits neither child. `joint_support_bound` gives the multi-root bound with distinct ANDs plus these disagreement nodes. `separate_witness_cluster_charge` permits independent witnesses whose union is not independent, provided the aggregate trace pays these nodes. The remaining missing theorem is a payment of disagreements within the actual residual budget.

Two computational selector examples were checked on full truth tables: semantic-cluster-obstruction.py (19 inputs) and semantic-cluster-lambda-obstruction.py (23 inputs, adding a unique raw-bank owner per OR). The latter checks all 8,388,608 assignments efficiently with truth-table bitvectors. Reader-centre union has size8 but shared AND union plus2 payloadroots has size7; four OR disagreements repair the bound. Unique bank owners and C4 do not force compatible choices. These payloads are edge-inactive, so these are NOT counterexamples under constrained-minimum consequences and NOT gap refutations.

Geometry: banks owned by a centre already in N(a) have raw vertices hitting at most that one centre in N(a). Multi-label banks with owner outside N(a) form C6 paths. For a common-mask cluster Z⊆N(a), non-a residual neighbourhoods are disjoint and form a star forest, so there is one distinct leaf per edge; since Z is already in the chosen top-centre cover, these edges require no additional cover vertices. Global overlap between different mask clusters and actual bank factoring remain unresolved.

## Final status: exact unresolved global payment

All checked semantic sources are frozen. The latest normalization source is `semantic-masked-witness.lean`; the latest aggregate trace source is `semantic-cluster-disagreement.lean`. Earlier files in each chain are superseded namespace snapshots, not independent modules to concatenate. Full build outputs are retained in task scratch and supplied to the parent for preservation. No semantic result proves or refutes the full posted statement.

The algebraic route now has a checked extraction from an accepted edge outside the selected top-centre cover K: on the chosen singleton raw side of its top AND, an OR-reachable AND payload accepts the edge, and the opposite raw bank gives exact clean-reader implications. The common-witness trace counts shared AND ancestors only once. For incompatible negative witnesses, however, the joint trace needs additional OR disagreement gates D. There is no checked proof that D can be paid by the available outside-large-lambda OR gates, raw-accounting surplus, or repeated-centre surplus. The K-aware residual completion has exposed the correct smaller budget, including only genuinely new cover vertices, but has not discharged this payment.

Canonical negative assignments partially control lambda gates. For a row centre z and a raw point bank owned by a different line y, C4-freeness supplies a raw neighbour of y outside N(z); it is already true, so the actual bank wire is saturated before and after toggling a leaf of z. This does not cover a line bank owned by a point: its raw lines can remain false while an internal nonlinear payload responds to the point-leaf toggle. Nor does it remove payload merges in a bank owned by the row centre itself. Thus the stronger assertion that every free lambda gate is unary or insensitive is unjustified.

The two obstruction families must remain distinct. The 13-gate bank-factoring regression is AO2, T0, TopForm, has every gate contextual-edge-pivotal and every OR branch contextual-edge-essential, but has an explicit 7-gate equivalent. It defeats unconditional local bank factoring under those necessary minimum properties. The 19-input and 23-input selector regressions concern incompatible witness traces; their payloads are edge-inactive, so genuine constrained-minimum activity excludes them. The 23-input version additionally supplies unique bank owners without violating C4-freeness. Neither family is a refutation of L-meta-4675, and neither shows the residual sum inequality false.

A restricted possible continuation is to count distinct covered raw leaves within one common-mask cluster Z⊆N(a), omitting the shared a. C4 gives distinct ownership of those leaves, so the duplicate-a raw-incidence overcount in the 13-gate example disappears on tests with a=false. Turning this into a proof still requires a transformation preserving all useful side outputs, a charge for opposite-part lambda payloads, and an allocation that does not reuse gates across different mask clusters. No such transformation or allocation was obtained in this attempt.
