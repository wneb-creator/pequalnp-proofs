# L-meta-4970 library route

## Checked semantic interface

`/tmp/oec/pequalnp-pilot-99/gap4970/library_route/SemanticSupport.lean` is frozen, 156 lines, 6433 bytes, SHA256 `382498a7ac184c9c633816973766263a4cd2b0eb9a7c4c73d8d485e4696ecacc`. Lean compilation and olean export exited 0; complete stdout/stderr are empty files `semantic-support.stdout` and `semantic-support.stderr` beside the source. Namespace `PEqualNP.Outside.L_meta_4970.SemanticSupport`; imports only Mathlib and PEqualNP.Defs.

The list-wire evaluation and monotonicity helpers are adapted from checked `L_meta_2606.lean`, from `wf` through `mono2`. The new lemmas are:

- `wire_mono`: every wire of an AO2 circuit is monotone in its input assignment.
- `support_of_false_complement`: if a wire is false at the assignment setting exactly inputs outside S to true, every singleton input making that wire true belongs to S.
- `below_disjunction_iff`: false at that complement assignment is equivalent to the wire implying the disjunction of S.

This supports the star-OR counting route: an AND gate false at the complement has a false operand, allowing an uncharged single-predecessor step; an OR gate false there has both operands false. Sat_encoding owns the ensuing accounting proof.

## Existing library census

Only checked L4791 mentions TwoColour.tCount: it gives a T=0 realization of any singleton-false AO2 function at approximately sixfold cost. Thus T=0 is a syntactic restriction on raw-input OR reach, not a claim that all semantic OR ancestors are pure.

L7649 `merge_bound` (lines125–219) counts set-labelled DAG merges; `leaf_budget` (703–803) groups pure OR leaf sets by their unique C4-free center but assumes the relevant non-below-output gates are OR with similarly non-below operands. Its `top_budget` (639–684) and L2237 `s2233` count OR gates combining top AND terms. L2237/L4897 full lower bounds additionally assume read1.

L5879 lines18–82 give a compact generic `smallSupport` lemma: k binary gates and r queried output wires depend on at most k+r input wire indices. Root is using this for elementary one-side star cases.

No full L4970 proof is claimed. Remaining central connection: bare star-OR witnesses may be unused or unrelated to productive AND paths; selected witness centers must be charged against gates joining products and combining outputs, without assuming read1 or clean normalization.

## Checked essential-input and star cases

`EssentialSupport.lean` (173 lines, 7164 bytes; SHA256 `5a62d9a6da7765e5635525be25a07b25c2f58d28bef53868b67459b562d3a29e`) compiled/exported with exit0 and empty `essential-support.stdout` / `.stderr`. It adapts checked L5879's 65-line `smallSupport` argument and adds `essential_bound` for any finite subset of essential inputs, followed by `edge_input_essential` and `active_bound` for the active vertices of a bipartite edge function. No monotonicity or C4-free assumption is required; FanInTwo suffices.

`StarBase.lean` (123 lines, 4798 bytes; SHA256 `dcca2e227f23c5647e131809341318035755162a5ddf7084db321a1f575e3b4c`) compiled/exported with exit0 and empty `star-base.stdout` / `.stderr`. Development-only import EssentialSupport must be inlined in the final file. `star_cover_bound` proves the posted cover inequality when every edge shares one row or one column. `small_side_cover_bound` proves it whenever p≤1 or l≤1, including empty graphs. Both require only FanInTwo and exact edge-function computation, so all other posted hypotheses may be ignored in these cases.

`EssentialStar.lean` is the standalone concatenation with only Mathlib and Defs imports, 289 lines, 11772 bytes, SHA256 `7ee79c0d4e15da23c66e9b8dea991aa25ac5a38ec2d8947555cf2f82cafa4226`. Compilation and olean export exited0 with empty complete `essential-star.stdout` / `.stderr`; this is the preferred integration artifact.

## Primary-literature audit, read 2026-11-25

No directly applicable theorem or counterexample was found for the exact T=0 plus bare-star-witness statement. The following are verified at the linked primary documents; none is being used as an unproved Lean assumption.

- [Jukna, Lower Bounds for Tropical Circuits and Dynamic Programs, Remark10](https://arxiv.org/pdf/1406.3065), printed p19: explicitly distinguishes a multioutput linear operator from its single-output bilinear form. It states an |A|/(4k^3) multioutput lower bound for k-free matrices, says the corresponding general Boolean single-output bound was unknown there, and gives |A|/(2k^3) for tropical/multilinear/arithmetic models. The PDF header has arXiv v2 dated2014 and an internal date2018; this is a statement about that source, not a verified current impossibility result.
- [Jukna, Notes on Boolean Read-k and Multilinear Circuits](https://web.vu.lt/mif/s.jukna/ftp/readk-submit.pdf), Theorems1–3 and Lemma9: read1 agrees with relevant homogeneous arithmetic/tropical models; read2 can be exponentially more efficient, using the all-rows/all-columns nonempty matrix function. This function is not the quadratic edge function here. The paper contains no occurrence of the word quadratic, and supplies no direct bridge from T=0 to read1.
- [Jukna, Disproving the Single Level Conjecture](https://web.vu.lt/mif/s.jukna/ftp/single1.pdf): the separation constructions use saturated extensions with within-color cliques. Consequently those examples do not satisfy bipartite C4-freeness. Its single-level estimates therefore cannot simply be transferred to the present unrestricted AND/OR circuit.

### Strength check from lower_bound agent

The following is our mathematical inference, not a theorem attributed to a paper. Replace each OR(a,b) in an arbitrary monotone circuit by AND(a,a), AND(b,b), OR of those two outputs. Every OR now has empty raw OR reach; cost is at most triple. Append dead pure OR gates on pairs of neighbors covering each left neighborhood. For even left degrees this costs exactly |E|/2. The augmented circuit satisfies the posted bare-star existence hypothesis and T=0. Therefore a proof of L4970 would imply 3|C|+|E|/2≥|E|+tau−1, or |C|≥|E|/6+(tau−1)/3, for every such C4-free graph. On regular projective-plane incidence graphs this is superlinear in the number of vertices. Thus the added syntactic/witness assumptions do not reduce the task to a known easy accounting theorem: the witnesses may be dead and inexpensive. This is not a refutation and does not show the statement false.

A search through recent primary literature did not locate a theorem resolving that exact missing single-output bound. Any claim that the bound remains open in2026 is UNVERIFIED: historical sources plus absence from a search do not establish current research status.

## Checked partial from the exact posted witnesses

`EdgeSupportCard.lean` is frozen, SHA256 `680c3bded93abba2cd8d2a9e51bc5df4a9013e566b75789512ab34a6bceaf24b`, with empty complete `edge-support-card.stdout` and `.stderr`; compilation produced an olean. Its generic finite injective orientation proves that edge count is at most the sum of endpoint support-union sizes whenever each edge is covered at one endpoint.

`PostedWitness.lean` (117 lines, 5789 bytes) is frozen, SHA256 `a491d696e26db2172a2a569359895ee72146a7fdab7eac488e20d9351e2eb37a`. Compilation and olean export exited0, with empty complete `posted-witness.stdout` and `.stderr`. It imports the checked development modules SelfChargedBudget, Neighbourhoods, and EdgeSupportCard. `posted_edge_or_bound` assumes exactly AO2, the posted C4-free condition, and the posted per-edge pure-OR witnesses; it proves `E.card ≤ 2 * (orWires (p+l) C).card`. It does not assume the witness gates are live or related to the output. Neither target correctness nor T=0 is used.

For each center c, take every OR wire charged to its neighborhood. A posted semantic pure-OR witness has exactly its stated singleton support, is false outside that neighborhood, has support size at least2, and is therefore a member of that charged family. Its endpoint is included in the support union. EdgeSupportCard gives the edge-count-to-sum bridge; sat_encoding’s checked SelfChargedBudget bounds the sum by twice the number of OR gates, using the checked C4-free neighborhood intersection lemma.

`PostedEdgeBound.lean` is the standalone concatenation of those four checked sources, with only Mathlib and Defs imports. Its standalone compilation and olean export exited0, with empty complete `posted-edge-bound.stdout` and `.stderr`; no full L4970 proof is claimed. The remaining required conclusion is the much stronger joint bound `E.card + vertexCoverSize ≤ C.size + 1`.
