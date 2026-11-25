# L-meta-4970 semantic route

## Frozen checked components

- `gap4970/reduction_strategy/StarUniqueness.lean`, 77 lines, SHA256 `25ebaee138b5b21888ba5a96128682681ae21022a7f44b5368d8221dd140522a`. Lean exit 0, complete stdout/stderr empty. Imports only PEqualNP.Defs. Identifies pure-OR leaf sets from singleton valuations; excludes equality of nonempty point and line ORs; proves a C4-free star with at least two leaves has a unique center, hence equal semantic line-OR wires cannot serve different point centers.
- `gap4970/reduction_strategy/EdgeAssignment.lean`, 43 lines, SHA256 `0c411a273c5493662cc0fe47c361cf510d393c1e6eecf0ddbb31c87e0b53c6ff`. Lean exit 0, complete stdout/stderr empty. Imports only PEqualNP.Defs. Selects an actually serving endpoint for each edge, obtains a vertex cover as the image, nonempty assigned-edge fibers, and exact identity `E.card + S.card = sum over S of (assignedFiber.card + 1)`.

Sources and logs are under `/tmp/oec/pequalnp-pilot-99/`; both checked files are frozen. Root owns lease, target edits, review and push.

## Definition hazards

`tCount = 0` constrains syntactic OR-reach, which stops at every AND. It does not imply semantic singleton supports are monochromatic: an allowed duplicate-input AND can hide an input before a mixed semantic OR. Any argument replacing syntactic OR-reach by semantic support needs an explicit charge for the intervening AND.

The star witnesses need not be read by the output. An ordinary minimum cover among centers appearing in any witness is insufficient: a selected center might not serve an assigned edge. The assignment helper instead retains the edge-specific serving relation.

## Counting obstruction

Sat_encoding owns the pure-OR witness cone cost. Multiple disconnected witnesses at one center give leaves minus components, not leaves minus one. Overlapping witnesses at the same center may be grouped through shared leaves. Different centers on one side share at most one leaf.

Let K count star components and d their total leaf incidences. Pure-OR construction gives a putative cost d-K. The remaining required inequality is `outside cost >= K + tau - 1 - (d - E.card)`. Lower_bound has a C6 example with dead opposite stars refuting the stronger version without the overcoverage correction. No such outside-cost inequality has been proved here.

An unused star subtree joins inputs already linked to the output and therefore creates undirected cycles. This suggests a connectivity charge, but plain connectivity is insufficient: for C6 with three stars it misses two gates needed by the semantic product-and-union structure.

## Local surplus idea, unproved bridge

Every center of a star with at least two leaves has degree at least two. C4-freeness separates its neighborhood from every other vertex's neighborhood. The previous Surplus proof `sem_dom_pure` only uses this separation for the selected vertex, so it can be localized even when other graph vertices are leaves. A center appearing in another star's multi-label carrier should therefore force an earlier pure-center branch. This may supply a reserve charge that syntactic raw-reader arguments miss. No formal local adaptation or completed cost bridge was added.

Do not assume every selected center has a raw reader outside all star cones: ANDs may reconstruct its singleton behavior with extra higher-degree terms. The branch/merge cost, rather than a raw-reader count, must pay for that possibility.

## Literature check

Read on 2026-11-25: https://pequalnp.com/papers/note-1, prior-work section. It distinguishes monotone single-level bounds from arbitrary-circuit bounds; it supplies no exact unrestricted `|E|+tau-1` theorem usable here. The proposed general T=0 bound without the star-witness premise would be much stronger: every input can be hidden behind an AND copy, making every OR reach empty at linear additional cost. Therefore the bare-free witness premise is essential to this route; it cannot be discarded casually.

## Fifteen-minute alternative-strategy pass

A minimum serving-star family does not supply a matching saturating its centers. Concrete obstruction: subdivide every edge of K4. There are six degree-two edge vertices A and four original vertices B. If the available witnesses are only the six ORs of each A-vertex's two B-neighbors, all six A-centers are forced by the serving relation, although the ordinary minimum cover has size four. The canonical A-star circuit realizes this configuration with 17 gates. Every star can have private edges without a matching of all six centers.

Choosing an ordinary minimum cover S and a maximum matching instead gives each selected center a distinct matched neighbor outside S. Every witness star centered outside S has all its leaves inside S. This might combine with localized pure branching, but the reserved branch can already be used to distribute a center among witness cones; adding it again would double-count. An additional merge or consuming-position charge is missing.

A possible one-sided subproblem is: treat arbitrary line-only functions as free, and prove a C4-free edge function with A active point variables of degree at least two needs at least 2|A|-1 gates involving point variables. Combined with a pure line-OR witness cost |E|-|A|, this would close a one-sided case. It must count all gates involving points, not just AND gates: the subdivision-K4 example computes the output with four line-centered ANDs despite six point vertices. No proof of the required total-gate bound was found, and the original mixed-side serving family remains harder.

Counterexample agent was asked for bounded C8 and subdivided-K4 searches in the superclass without T=0 or witness restrictions, with full premise checking before any claimed counterexample. Prior C6 seven-gate UNSAT control rules out the smallest candidate; an UNKNOWN result gives no proof.

## Checked append construction

`AppendPairs.lean`, 248 lines, SHA256 `90ce24e54415bfefb21296fe9154803ddb42b6e737f5835419336afcbd3770f4`, compiled with exit 0 and empty complete stdout/stderr. Frozen source imports the separately checked `Shield` scratch module; final assembly must inline that module once.

Namespace `PEqualNP.Outside.L_meta_4970_aux.AppendPair`. `Pair p l` is a point together with two lines. `PairValid E pairs` requires distinct lines and both incidences. `PairCovers E pairs` requires each edge to occur in a pair at its point. `append_main` assumes the original circuit is AO2, has T=0, and has a valid output index. It appends OR gates reading the two raw line inputs, preserves the old output, has exact size `C.size + pairs.length`, preserves the computed function and T=0, and supplies the full posted line-star witness for every edge.

`output_valid` derives the output-index bound from a nonempty edge set and correctness. This premise cannot be omitted: IsAO2 does not constrain the output, and appending gates can turn a formerly invalid output into a valid new OR. The empty-edge case of the desired lower bound is handled separately with an empty cover.

The file also proves generic OR-reach and OR-input prefix stability under gate appending. No assumption that the new gates are used by the old output is made.

## Potential/dual-count replan

No completed potential proof was found. A precise obstacle is exposed by the checked append construction: one new raw pair-OR gate supplies two previously missing serviced edges. A potential counting serviced edges at unit weight therefore needs a compensating negative component term. The natural construction potential is d-K, leaving exactly the unresolved output contribution K+cover-1-(d-E). On the append family this contribution is of order E/2, so the output part cannot be discharged from star uniqueness or input connectivity alone.

A quadratic coefficient-rank approach is also incomplete. The C8 bipartite adjacency matrix has rank three over characteristic zero while its minimum cover is four; a rank charge cannot supply the full cover term there. Boolean/nonnegative rank is the relevant stronger quantity for a single-level decomposition, but arbitrary nested ANDs and the negative quadratic terms introduced when expanding OR prevent a direct transfer. T=0 is syntactic and does not simply remove those terms, because AND copies can hide singleton behavior.

Primary source read 2026-11-25: Jukna, *Disproving the Single Level Conjecture*, author PDF https://web.vu.lt/mif/s.jukna/ftp/single1.pdf. Section 8, Problem 8.2, asks for a superlinear monotone fan-in-two lower bound for an explicit quadratic graph function. The checked transfer would imply an order n^(3/2) bound for incidence graphs of odd-order projective planes: each left degree q+1 is even, E=N(q+1), and the number of inputs is 2N. This is an inference from the transfer and plane parameters. The historical problem is verified from the 2006 paper; its current 2026 open status is UNVERIFIED from that source. Lemma 3.7 in the same paper concerns OR-only Boolean-sum circuits and is not an AND/OR normalization theorem.

The counterexample agent's bounded C8<=10 and subdivided-K4<=14 unrestricted searches were UNKNOWN, not proofs or refutations. Its 11- and 15-gate controls were independently truth-checked and satisfy T=0 and semantic star coverage.
