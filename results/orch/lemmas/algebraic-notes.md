# Algebraic route: L-meta-4675

## Research checked 2026-11-25

Read https://pequalnp.com/papers/note-1 through the web tool. Its prior-work section reports that general monotone Boolean-circuit lower bounds for explicit bipartite C4-free edge functions are substantially harder than arithmetic, tropical, multilinear, or single-level bounds. The accepted factor-six compilation to T=0 means the current exact bound would imply a general constant-factor |E| bound. This is context, not a disproof.

## Degree-two extraction

For a monotone wire function f, define its singleton support S(f) and its cross-pair truth set Q(f). On OR, both are unions. On AND, singleton support is intersection; cross-pair truth sets intersect. An edge accepted at output can be traced backward through ANDs until a first multiplication of its endpoint singleton witnesses. That originating AND determines a rectangle from the two singleton supports. However this rectangle need not be contained in E: subsequent ANDs can filter false edges. Thus charging one star per originating AND is invalid without controlling the filtering cost.

The exact remaining obstruction is filtered rectangles from dirty AND gates. No valid gate-count invariant has emerged. In particular T=0 controls syntactic OR-reach, not semantic singleton support: AND buffers can hide singleton supports and permit later semantically mixed ORs.

## Potential alternate proof route

Restrict all line inputs except one to false. The output is the OR of the point-neighbourhood of that line. Thus any original circuit induces a simultaneous family of linear monotone outputs on the point side, with restrictions of every gate. C4-freeness means any two distinct such neighbourhoods intersect in at most one point. An appropriate shared-circuit lower bound for this family, charging line-dependent selection and Boolean intersections, might yield the desired inequality. Simply replacing ANDs by intersections of singleton supports loses higher-degree terms and is not a valid circuit transformation.

## Simultaneous restriction analysis

For a fixed line b, use the canonical negative assignment: line b true, all other lines false, and exactly the points outside N(b) true. A false AND can choose one false child; a false OR retains both children. Backward pruning from output yields an OR-only sub-DAG for OR N(b). The difficulty in adding these row bounds is that one original gate is a different function under each line restriction. Shared OR nodes can support different point sets after line-dependent AND choices. C4-freeness controls literal shared linear outputs, but not these specialized functions.

The site prior-work paragraph reports the exact sum(|S_i|-1) gate lower bound for a fixed family of linear OR outputs whose sets intersect pairwise in at most one element. Turning the specialized row circuits into one shared multi-output circuit with a controlled global cost remains unproved.

## Separate count checks

The plausible split OR_count >= |E|-1 and AND_count >= tau has no proof here. Accepted L_meta_2399 proves the general C4-free AND bound only when tau<=5; L_meta_634 establishes Fano AND-count7 by a long dedicated proof. Accepted L_meta_7241 obtains the full edge+cover bound when every AND gate rejects every nonedge pair, a stronger semantic restriction than T=0. Consequently neither separate count bound should be silently treated as elementary.

## Checked components

algebraic-mask.lean and algebraic-certificate.lean both compiled with pinned Lean, exit0 and empty stdout/stderr. The second proves semantic verification from positive edge pairs and canonical independent-extension negatives, plus the exact one-line restriction identity. These are helpers only; they do not establish the target lower bound.

## Bipartite pair-clean bridge

At 2026-11-25T17:24:46.605642+00:00, the first algebraic-bridge.lean version compiled. It reuses the checked PairClean core and constructs graph E on Fin(p+l), proves C4-freeness, identifies graphFun with the desk edge function, and translates graph vertex covers into the exact conclusion. The remaining extra hypothesis is that every AND gate rejects every nonedge pair of graph E. This hypothesis is not derived from T=0. An exact edgeFinset.card=E.card lemma was added and is being rechecked.

Current bridge including exact edge-cardinality equality compiled successfully (exit0, warnings only). Complete logs: /tmp/oec/pequalnp-pilot-163/algebraic-bridge-2.stdout and .stderr. For aggregation, append only the Bipartite namespace at line946 onward; the preceding944lines duplicate library-pairclean.lean.

## Residual charge route and corrected calculation

From L_meta_4183, write t=|tops\centreless|, c=|centreless|, j=|junk|, o=|orN\lam|, and U=Ustar. The counting inequality is |E|+t+2c+j+o<=|C|+|U|+1, while t star centers cover E\U. Therefore |U|+tau(U)<=2c+j+o is a sufficient missing residual bound. The accepted theorem assumes unrestricted IsLeastAO; our normalization only gives minimality inside T=0, so its leastness-dependent component needs adaptation.

CORRECTION: I initially reported an8gate double-star circuit as a residual counterexample, but the count was wrong. With point inputs a0,a1,c and line inputs b0,b1,d, let h=(a0 OR a1) AND (b0 OR b1), t1=(c OR h) AND b0, t2=(d OR h) AND a0, and output=t1 OR t2. Its graph has five edges. I incorrectly counted o=2, omitting the two setup OR gates for h. They are outside lam because the dirty AND h blocks top-side OR reach. Correct counts are |U|=3, tau(U)=2, c=0, j=1, o=4: the proposed residual bound holds at equality5. NO COUNTEREXAMPLE was found. Parent, structural agent, and counterexample agent were informed immediately. Future counterexample labels require independently computed finsets/counts.

The corrected calculation suggests setup OR gates outside lam provide exactly the missing payment. If both setup ORs are placed in lam using extra pure-star readers, C4-freeness restricts their overlap with residual edges and may force a cycle exchange.

## Residual accounting adaptation

`algebraic-residual.lean` is a checked 1425-line / 65157-byte adaptation of L_meta_4183. Its `Residual.main` takes only AO2, C4-freeness, and the explicit balance `(orT G C).card + 1 = (tops G C).card`. It returns both the original counting inequality and the minimum-cover bound on the already-covered edge graph. The entire unrestricted S98 minimum-circuit argument was removed; `S90.top_facts` now assumes AO2 only, which is all its proof uses. Full check: algebraic-residual-1.stdout/.stderr, exit0.

The separate `algebraic-tree.lean` is being checked to derive balance from constrained T=0 minimality, TopForm, output-last and no-unused-gate facts. Those final two structural premises are being supplied by library agent; no unrestricted leastness is substituted.

For free lambda banks, a canonical negative input may help: for residual edge a-b, turn on line b only and all points outside N(b), then toggle a. A pure lambda point-bank containing a has a star centre z distinct from b (otherwise a-b would already be covered); if its raw set has at least two points, C4-freeness supplies a different point outside N(b), keeping that bank true across the toggle. Pure line-banks are unchanged. Caveats: singleton lambda raw sets have no backup; actual lambda wires may contain hidden dirty payload, so a pure-bank-plus-payload factoring with controlled OR cost remains necessary.

Both follow-up files now compile with exit0. `algebraic-tree.lean` has a new TreeCount namespace after its copied1812-line Lift prefix; `TreeCount.balance` proves the exact top/OR balance from constrained T=0 minimum plus output-last, no-unusedgate, singletonfalse, computes and TopForm. Full logs algebraic-tree-6.stdout/.stderr. `algebraic-residual-complete.lean` adds a finite minimum-cover construction and `Residual.complete`, turning a residual cover S with |U|+|S|<=2c+j+o into the full desired graph cover bound. Logs algebraic-residual-complete-1.stdout/.stderr. The residual cover inequality is still an explicit hypothesis, not proved.

## Checked pure-bank pivotal witnesses

`algebraic-bank.lean` (77lines) compiled exit0 with empty algebraic-bank-2.stdout/.stderr. For a residual point-line edge a-b, points outside N(b) true and only line b true form a negative input; toggling a makes the graph function true. Every pure point OR-bank S of at least two vertices remains unchanged if S lies in a star at z and a∈S implies b≠z. This is simultaneous over an arbitrary bank family. Singleton bank outputs are not supplied as independent free inputs; duplicate raw inputs must instead be eliminated by renaming. Actual lambda wires can have dirty payload and are not covered by this pure-bank lemma.

Search found accepted L_meta_3760 (10039lines), duplicated L_meta_8725, proving a bipartite C4-free unrestricted minimum cannot have exactly one junk gate. Its proof uses residual edge classification, mixing-gate injections, and star-cover upper bounds; it does not eliminate arbitrary interacting dirty gates. Some replacement-by-raw-wire steps would need separate T=0 preservation, while pure counting cases may be reusable.

## Fully discharged constrained accounting and exact conditional target

`algebraic-residual-closed.lean` compiled exit0. Its final Residual namespace derives balance from SemanticFold.least_output_last/least_no_unused and TreeCount.balance; `constrained_main` now proves the L4183 accounting with only constrained T=0 minimality and TopForm (plus AO2, computes, nonempty graph and C4). `constrained_complete` needs only the explicit residual cover certificate beyond those normalized hypotheses.

`algebraic-bipartite-reduction.lean` compiled exit0. Its final namespace defines Residual.Certificate and proves the exact posted bipartite conclusion assuming certificates for normalized circuits. It handles E empty, normalizes with Normalized.exists_top_form_pair_active, uses constrained_complete, and translates graph/cardinality back. This is an internal conditional reduction, not a proof of the posted theorem; reductions are closed for our lease.

`algebraic-residual-large.lean` also compiled exit0. Its final namespace defines largeLam={k in lam | rawsupportcard(k)>=2} and proves main_large, replacing orN\lam by the larger charged set orN\largeLam. This uses assemble2 with free-stop B containing every rawsupportcard<=1 gate. Thus singleton-raw lambda payload mergers are charged without any additional minimality assumption. A raw spanning-forest refinement of selected large-lambda gates remains unproved.

Frozen unique extraction slices (all through EOF): tree line1814 (266lines); residual-complete line6 (1458lines); residual-closed line4988 (55lines); bipartite-reduction line5168 (51lines); residual-large line1427 (163lines). These total94317 bytes.

## Separate cover-charge obstruction

The validated8gate double-star example above has tau(U)=2, c=0 and j=1. Therefore the separate inequality tau(U)<=c+j is FALSE for general T=0 TopForm all-pair-active circuits. The SUM residual inequality still holds at equality5. This was explicitly highlighted to parent and counterexample agent after revisiting global masking-charge arguments. It does not refute the separate bound under constrained minimum, since this8gate circuit is not minimum. Cover vertices may need OR/slack payments in a general circuit argument.

## Shared-payload obstruction and centre-hit charge

Independently reevaluated semantic agent's13gate shared-payload circuit using algebraic-bank-obstruction-eval.py: all128 truth rows, explicit C4 check, exact top/junk/lambda/U sets. It has t=2, lambda=largeLam={8,9}, coverededges=4, and rawslack delta=t+|lambda|-|covered|=0. The free gates already form one-edge raw forests at distinct centres. Therefore choosing per-centre forests and retaining rawslack alone does not fix payload duplication across centres; upstream dirty-gate cost or full minimum must be used. Residualsum4<=8 still holds, so this is not a target counterexample.

The next route is a dirty-witness charge. If k distinct reader centres all neighbour raw a, payload f is monotone, and f(y) AND y(z) always implies the target for every centre z, then any independent f-witness x with x(a)=false contains at least k distinct neighbours. `algebraic-centres.lean` proves this (exit0, centres-2 logs). The independent witnesses might all contain a, but semantic agent has now checked a masked-region cofactor transformation: when all external region reads are OR-masked by raw a, minimum forbids any direct read of a inside the region. AND proof-trace support counting is being attached to turn the witness size into a distinct-gate lower bound.


## Actual trace charging, 2026-11-25T18:22:20.594944+00:00

Checked and frozen `algebraic-reader-charge.lean` (3142 lines; logs algebraic-reader-charge-2): an independent dirty witness avoiding shared raw a, exact clean-reader implications, and a payload gate in the cone of a later AND give number of distinct common-a reader centres at most junk AND count + 1. Trace picks one true OR child and both AND children; support is a successful subassignment. TopForm injects all relevant AND ancestors into junk. This does not assert that arbitrary dirty witnesses are mutually compatible.

Checked and frozen `algebraic-cluster-charge.lean` (logs algebraic-cluster-charge-1): extends actual trace to a finite union of root cones. `manySupport_step` fits the shared multi-root DAG bound; `manyAnd_card_le_junk` injects distinct union-cone AND wires once into junk. `common_reader_centres_le_junk` applies semantic agent's abstract common-witness cluster theorem to actual circuit gate functions, proving |union Z_r| <= |roots| + |junk|. It assumes one common independent assignment accepting every payload and avoiding the shared raw input a.

Remaining obstruction: independent witnesses for different payloads may be incompatible. Semantic's selector example shows that alternate OR choices inside lambda2 banks can select different centre labels, although that example has edge-inactive payload gates and is excluded by current normalization. A lambda2 bank whose unique star centre also neighbors a can hit only that centre among N(a), by C4-freeness. Thus only owners outside N(a) generate genuine multi-label ambiguity; two labels create a 6-cycle a-w1-u1-z-u2-w2-a. Need charge that ambiguity using edge activity, paid mixing ORs, or cover exchange.

Potential improvement of residual certificate (semantic observation): the top-star centre cover K already covers residual edges incident K. An additional cover is needed only for residual edges disjoint from K. Our earlier |U|+tau(U) certificate overpays this part; retain actual |K union S| and raw accounting slack instead. Not yet a proof of the missing cost inequality.


## Concrete existing-cover residual refinement, 2026-11-25T18:27:13.764811+00:00

`algebraic-residual-cover-union.lean` is checked and frozen (logs algebraic-residual-cover-union-3, exit0). It extends the checked large-lambda accounting with a concrete `starCentreSet K`: at each noncentreless top select the left raw operand when its cardinality is at most1, otherwise the right raw operand; take the union. C4 and clean-top facts give |K|<=t; K covers every edge outside Ustar.

Let delta=t+|largeLam|-|E\U| and allowance=2c+j+|orN\largeLam|+delta. `residualAllowance_exact` proves exactly C.size+1=|E\U|+t+allowance, retaining raw accounting slack. `complete_star_centres` proves the desired graph bound from a residual S that covers ONLY U edges with both endpoints outsideK, requiring |U|+|S\K|<=allowance+(t-|K|). Thus neither overlap with the existing cover nor repeated star centres is charged twice. This remains a conditional completion; the residual inequality is still open.

Useful orientation for future charging: at a centred top (k OR P) AND (OR_S OR Q), k is already in K. Edges from k AND Q need edge-count payment only. Residual edges disjointK can arise from P AND OR_S, where S supplies genuinely new cover choices and the common-mask centre/AND trace applies with mask k, or from P AND Q, a double-payload term that needs its own gate/cover budget. Two payload insertion OR payments may fund such a double-payload term, but arbitrary shared lambda payload factoring has not been proved.


## Actual outside-cover payload decomposition, 2026-11-25T18:30:33.629386+00:00

`algebraic-outside-payload.lean` checked and frozen (logs algebraic-outside-payload-2, exit0). `accepted_without_raw_has_and` shows that an accepted wire with all raw OR-reachable inputs false has an accepted AND gate in its OR-reach. `orReaches_eq_or_cone` and `operand_payload_cone` put that payload in the top's actual AND cone. `payload_clean_readers` derives the exact clean-reader implication for all raw inputs in the opposite operand from top cleanliness.

`outside_selected_side_payload` applies these facts to a noncentreless top accepting any pair whose two endpoints lie outside the concrete starCentreSet K. It chooses the same side as K's definition, whose raw support lies in K, so no raw leaf on that side accepts the pair. It extracts an accepted AND payload on that side, its cone ancestry, and all opposite-bank clean-reader implications. This is an actual syntax/semantics bridge, with no lambda-bank constancy assumption. C4-top facts separately ensure that this selected raw side is a singleton; the extraction itself only needs its containment in K.

The main gap is still substantial: aggregating charges for many such singleton-side payloads and for double-payload terms without reusing shared junk/OR costs. K-aware accounting removes artificial repeated-cover costs but does not establish this global structural bound. No full theorem or refutation has been derived.


## Final frozen status, 2026-11-25T18:31:16.116453+00:00

All algebraic sources are frozen; no further proof branches are active. `algebraic-checked-inventory.json` records21 checked helper files, source hashes/line counts and complete diagnostic log hashes. Twenty have directly observed successful compiler exits; algebraic-and-many is additionally certified by its verbatim inclusion in the successfully compiled algebraic-cluster-charge source. The latest new outputs are the K-aware residual certificate and actual outside-K first-AND payload decomposition. There is no short completed route to the full theorem: globally pricing shared dirty payloads and double-payload terms remains unproved. These helpers and the corrected finite examples are partial progress only, and should not be submitted as a proof PR.
