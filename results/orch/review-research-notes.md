# Independent research-notes review

Verdict: PASS for the seven frozen artifacts below. The later subdivision/lift notes are mathematically consistent, with the provenance qualification described below. None of these artifacts proves or refutes L-meta-3451.

The final checker stdout is empty and stderr says only that the prebuilt Mathlib cache is missing. It does not report acceptance. The computational README correctly separates externally trusted solver evidence, UNKNOWN/interrupted outcomes, and fully validated SAT witnesses. It states the single-kind padding condition and does not claim the scripts are formally connected to Lean.

The L-meta-3760 audit was checked against the local accepted source and TopForm definitions. The general TopForm transformation preserves junk count; the general count retains Ustar; strengthened routing and bounds assume exactly one strong junk. IsAO2 has exactly two inputs per gate, and strong junk tests every independent assignment. Thus no unrestricted weak-clean normalization theorem is obtained by importing that result. The earliest-junk observation is a mathematical route, not a newly checked Lean declaration.

All 16 separator restrictions were independently replayed on all 16 Boolean assignments each. The seven-gate matching circuit computes its stated target exactly. Its nonempty restrictions have zero or two strong-junk ANDs, never one. The P4-to-star restriction and cubic interface example have the stated behavior. These circuits are used to disprove automatic preservation properties; the matching example is explicitly nonminimal and does not refute a minimum-circuit isolation theorem or the posted target.

The colored K4 lift was independently replayed over all 16384 assignments: 18 edges, C4-free, 13 essential variables, minimum vertex cover 6, and a correct clean 23-gate witness. The listed cover is valid. Adding the missing triple of color points makes every pair of seven points lie in exactly one of seven triples, confirming the Fano-minus-one-line description. No lower-bound circuit search is claimed.

Subdivision provenance: the local cycle theorem is lean/PEqualNP/MetaComplexity/L106.lean, not an Outside/L_meta_106.lean file. Its HasCircuitSize model is arbitrary fan-in-at-most-two AND/OR/NOT, including constants, so the formula is not restricted to single-level circuits. L106 states the exact cycle size n+ceil(n/2)-1 for n>=5; C12 gives17, C8 gives11, and C_(8k+4) gives12k+5. This review source-inspected that repository theorem, but did not build or audit its dependency chain. The notes should attribute the formula to repository L106 rather than imply it was independently kernel-certified in this job. This qualification was sent to the parent before publication.

The odd-subdivision vertex-cover formula follows by elementary accounting. For each path of length2k+1, at least k internal vertices are needed, and k+1 are needed if neither old endpoint is selected. Add one endpoint for every original edge left uncovered by selected old vertices, obtaining a cover of the original graph of size at most the new cover size minus k times the edge count. Conversely, a minimum original cover extends with exactly k internal vertices per edge. Thus tau_new=km+tau and m_new=(2k+1)m. SubdivPlan contains S4/S5/S6 statements and SubdivFwd proves S5; a proposition named StmtS6 is not itself evidence of a completed theorem. The notes do not claim an advantage-preserving circuit transfer.

The reviewed public artifacts contain no credentials or live lease identifiers. The main Lean source was unchanged by this review.

| File | Bytes | SHA-256 |
|---|---:|---|
| results/orch/checker-final.stdout | 0 | e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855 |
| results/orch/checker-final.stderr | 113 | ef42927aceadf270d24f09adbbb2d636153cb74f3353874a3b328b434816079a |
| results/orch/lemmas/counterexample-README.md | 4904 | 1ef78a3c1ce5bc1491d2ab3175a60220a474b16db7b847cb0437a7eefc7d6506 |
| results/orch/lemmas/global_3760_audit.md | 3780 | 78f16c9dbf98a6396c80d181a16ed301105c983e8251f4d1ac35966235e03224 |
| results/orch/lemmas/global_separator_audit.md | 3660 | ba120b2deb628eab9dffe0fb465ba5808be949d41345d990a22d115861aafe3b |
| results/orch/lemmas/global_separator_restrictions.json | 2046 | 4e6f6ed065c0e9f5f1e7e93b56f5494c790034095150c1a171725453f554fbde |
| results/orch/lemmas/counterexample_colored_lift.json | 2072 | fa550749a3e9e43c1fec0dbe7a12fbd033d39f07bdbfb68269d91a955fc9640f |

Reviewer: status_review. No proof or research source was edited.

## Revised cycle-source wording

PASS: the revised subdivision/lift paragraphs now attribute the cycle formulas to repository theorem L106, and the explicit qualification distinguishes source inspection from building or axiom-auditing that dependency chain. It identifies the unrestricted fan-in-at-most-two AND/OR/NOT model and treats the odd-subdivision cover formula as mathematical reasoning, not a proved statement-definition. Current NOTES.md is 45128 bytes, SHA-256 2d315b495e6eea18483017cb35beb35c8a8d17ebfee06caeada32c6e2172c649. This supplemental check covers the revised cycle/lift paragraphs and qualification; it does not expand the earlier review to later independently authored singleton-hoisting research.

## Singleton-hoisting section

Reviewed the newly added section against local L_meta_3710.lean, L_meta_5393.lean, L_meta_3653.lean, and the retained public per-lemma JSON for L-meta-5280 and L-meta-3456. The ten-gate clause witness is explicitly UNVERIFIED; L-meta-5393 instead exhibits ten- and six-gate circuits with the same five-edge function. L-meta-3710 proves the stated global-reader bypass under the singleton-v and all-neighbors condition, keeping the output index unchanged. It assumes IsAO2: backward-reading AND/OR gates with exactly two inputs. The parent was asked to include this model restriction explicitly before publication.

Within that model, the minimum-size corollary follows: a singleton-true AND cannot be the graph-function output, and a successful bypass would leave it unread and hence removable. Therefore each operand must miss some neighbor. The five-gate P4 circuit was independently replayed on all 16 assignments and computes ps OR pq OR rq; its first AND is singleton-true at p, and neither operand meets the neighbor condition. Its clean four-gate alternative means it is not a minimum-circuit counterexample. The notes correctly retain all these restrictions. L-meta-3653 and public L-meta-5280 have additional normal-form, operand, or partner hypotheses, as stated in the notes; neither cited result closes arbitrary sharing. No refutation of L-meta-3451 is claimed.

Final singleton-scope wording: PASS. Both the bypass statement and minimum-size corollary now explicitly use IsAO2, with backward reading and exactly two AND/OR inputs per gate. The final reviewed NOTES.md is 45222 bytes, SHA-256 bc0c253556ac49f9d72285a0ba397911ba3ad75074c78101e7260c120528f286. The supplemental singleton-hoisting section is now covered in addition to the cycle/lift and earlier research sections.
