# L-meta-2590 independent source audit

Updated 2026-11-25T15:16:44.314230+00:00

Read-only audit; no desk requests, git mutations, or proof-file changes.

## Existing reductions

- `R_meta_2590_1`: two finite-semantic suffix hypotheses. Give an arbitrary first AND or OR of at most two raw inputs for free; any monotone suffix of at most18 gates must fail one of30 extremal rows. Positive rows are the15 edges; negative rows are all15 maximal independent sets.
- `R_meta_2590_491`: compression to an AO2 circuit of16–18 gates with a selected guard wire no longer reading input0. Substituting input0 by x0 AND guard or x0 OR guard simulates the original. Two remaining row-exclusion hypotheses apply under singleton-neighbor-positive or ten pivotal-negative guard conditions.
- `R_meta_2590_932`: semantic traces of at most18 wires, with constants, ten inputs and one supplied binary gate. Three priority cases: free edge OR x0∨x1 (forbid raw nonedge ANDs); free nonedge OR x0∨x2 (also forbid raw edge ORs); free edge AND x0∧x1 (forbid every raw input OR). `replace_trace`, `mask_target`, `delete_nonedge` provide usable semantic deletion machinery.

No child-ID mapping was established before the subsequent SAT assignment. The exact hypotheses were read directly from all three checked reduction files.

## New upstream results

Audited final named statements of257 added meta files at FETCH_HEAD2af7128d. The258 changed-path census includes the local2583 partial absent upstream.232 additions concern7-variable NOT elimination. The remaining additions include9-variable general size lower bounds14–16 and12-variable monotone size≥19 (`L_meta_9734`), but no10-variable Petersen lower bound or any exact2590 reduction premise. None of the new9-variable graph lower bounds has the degree multiset of Petersen minus one vertex; direct graph-isomorphism reuse is therefore excluded. Complete extracted statements are retained in `/tmp/oec/pequalnp-pilot-103/2590-new-upstream-statements.json`.

## Useful positive reuse

`L_meta_4332` inputs/graph definitions at lines745–746 are byte-identical to `L_meta_6581` lines749–750. Its `monoRoot` proves `Impossible false graph15 inputs.toFinset`; the existing Geometry projection from the earlier Binary17 work needs no coordinate permutation. Communicated directly to lower_bound, who is deriving the monotone18 floor / first-AND19 bound.

## PR and history census

Fully paginated GraphQL census:1008 open PRs across11 pages; final hasNextPage=false, all JSON shapes checked. Only exact2590 mention: PR16055, https://github.com/open-goat/pequalnp-proofs/pull/16055. It proposes a fourth reduction `R_meta_2590_2.lean`,121 lines, head eedb2b4faa4d31ee7c5a3086c688aedd8f1be13d. It is not a completed proof. Its remaining hard premise is a conditional20 lower bound for least TopForm Petersen circuits with at least2 uncovered star edges, after assuming generic normalization/star extraction/count inequalities. The ≤1 uncovered-edge cases are discharged by finite vertex-cover deletion facts. Source and metadata retained under `/tmp/oec/pequalnp-pilot-103/2590-pr16055*`.

No exact `L_meta_2590.lean` exists in checkout or exact-path all-branch history. Existing reduction commits:55e8602e (#8191),98920d9e (#7763),97097ec9 (#4786). Public map snapshot13:57UTC lists2590 conjectural; this snapshot is stale and is not lease evidence.

## Scope cautions

Accepted Outside files cannot be imported into the target: copy needed helpers inside the target namespace, use only Defs/Mathlib imports. Keep the named file≤512KiB. A partial floor18/19 theorem must not be presented as the posted20 theorem. The occupied three-reduction capacity prevents treating PR16055 as a ready extra submission route.

## Later exact AND-count discovery and stopped equality route

Checked L_meta_635 (151435bytes2355lines) proves exact Petersen AndCountCircuit≥6, so the auxiliary five-AND test is redundant. Its `lower` at2305 first derives size≥5, then treats an earliest AND accepting an independent set and discharges a finite five-gate classification. `lift_slots` explicitly assumes size5 and four remaining gates; its Cap bounds do not extend to size6. `free_bound` only yields at least3 gates omitting each primary input, hence bare occurrence≤3 at size6. No equality rigidity/read1 theorem was found in this source. L_meta_905 additionally excludes≤6 gates if every vertex occurs in at most2 bare AND sides; this does not cover the size6 equality case.

The proposed separate OR≥14 complement is false. circuit_search found a23gate10AND13OR Petersen circuit, independently validated by this reviewer on all1024assignments; see or13-independent-review.json. A possible remaining count tradeoff is that six-AND circuits are read1, or otherwise require≥14OR. No such claim was proved. Before the lease expired, the missing-squarefree macro predicate passed positive/negative pinned sanity checks, but no unrestricted six-AND test started. All work paused at the parent's410 instruction.
