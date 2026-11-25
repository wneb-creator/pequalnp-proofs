# L-meta-4970 independent status and review

Public snapshot: 2026-11-25T15:40:11.300Z. Root alone holds the lease; this agent made no desk request and no git mutation.

## Posted goal and status

[L-meta-4970](https://data.pequalnp.com/data/lemma/L-meta-4970.6db39747a63b.json) is conjecture, with no public dependencies, used-by nodes, or attempts. Its only permitted import is `PEqualNP.Defs`. The target concerns bipartite C4-free edge functions, AO2 circuits, tCount = 0, and semantic star-OR coverage of every edge; conclusion is a vertex cover S with E.card + S.card <= C.size + 1. The semantic star-OR witness need not itself be read by the output.

## Existing PRs

Complete paginated structured GitHub search for 4970 found no open proof PR. Only relevant result: [PR12708](https://github.com/open-goat/pequalnp-proofs/pull/12708), closed unmerged, 24-line conditional reduction `R_meta_4970_7`. The checker comment explicitly says the step was not open to reductions, so the reduction would not be checked. It has no checked descendants.

Its actual source, preserved in `PR12708.external.lean` (external reference, not locally compiled), assumes two substantial results: a cover bounded by the AND-gate count, and E.card <= OR-gate count + 1. The body only combines them by arithmetic. It is not a complete proof with a formatting problem. Numeric search hits PR4970 and PR15238 are unrelated steps.

Searches for bare-free and tCount also surfaced no proof of this target. A query for stronger L3995 produced only an unrelated numeric PR hit. All raw API pages and stderr are retained.

## Nearby checked results and limitations

- [L3995](https://data.pequalnp.com/data/lemma/L-meta-3995.c90186fba816.json) is the stronger two-sided surcharge conjecture and remains open.
- [L4757](https://data.pequalnp.com/data/lemma/L-meta-4757.600647bb2293.json) is checked but assumes both normalization to no mixed OR and the complete no-mixed-OR lower bound; it only derives a star-list comparison. It cannot discharge L4970.
- [L1954](https://data.pequalnp.com/data/lemma/L-meta-1954.884b9497f7eb.json) assumes four THEOREM N steps before its served-count/cover bound. [L1952](https://data.pequalnp.com/data/lemma/L-meta-1952.9bc0db6a09a4.json) is likewise conditional.
- [L1713](https://data.pequalnp.com/data/lemma/L-meta-1713.b0d3fe5c8f30.json) and [L1949](https://data.pequalnp.com/data/lemma/L-meta-1949.dabb0921fda9.json) assume the stronger KM0 condition on AND inputs. tCount = 0 alone constrains OR reach, so the required implication is not definitional.
- [L4366](https://data.pequalnp.com/data/lemma/L-meta-4366.c0a0702a1982.json) is only an induction corollary assuming the individual two-colour OR removal step.
- Potential reusable ingredients, not direct solutions: [L4729](https://data.pequalnp.com/data/lemma/L-meta-4729.55b6167b929f.json) extended star-hull replacement; [L5403](https://data.pequalnp.com/data/lemma/L-meta-5403.0f26de232fc6.json) same-colour singleton-support coincidence for operands of ANDs below F; L5397/L5407/L5409/L5420 conditional rehousing/rebuilding and cost bounds. Exact statements are saved under nodes/.

No near-complete full proof rejected only for format was identified. No direct stronger checked theorem closing the goal was identified.

## Read-one obstruction review

Initial checked snapshot `ReadOneObstructionChecked.lean`, SHA256 ab53e3e4eae6fa7ff467a772a99ca950f9c711d7ab5f4b8ac87d1562127b05e2, is mathematically sound: a 3-gate circuit first computes x0 AND (x1 OR x2), then ANDs x0 again. It satisfies the posted hypotheses for the 2-edge star, while IsReadK 1 fails. The posted bound still holds, so this is not a refutation of L4970. Matching recorded compiler exit is 0.

Two global resource options lacked local `in` scope. Producer was asked to remove or scope these and freeze a newly checked snapshot; initial source is acceptable only as an explicitly partial artifact, not final-file format.

V2 APPROVED: `ReadOneObstructionV2Checked.lean`, 39 lines, SHA256 c6e6aca0419c1ac5a502065dc36a0796a6567ea2eeee7f121c4e44fdaa83baf5. Exact change is removal of the two global options and one blank line; matching fresh compiler log records clean exit 0. Mathematical meaning unchanged, source-format issue resolved.

## Next checked preservation batch

- `proof_strategy/StarCentersChecked.lean`, 165 lines, SHA256 `a6861c35df67044bf85bc78187a6f6db1e99faa0e52b307852439255e799d604`: APPROVED. Semantic OR equality and the no-C4 condition force a unique centre for each certified OR gate; opposite-side centres cannot share a gate. The final cover bound is by OR-gate indices, not AND gates. No AO2 or tCount premise is needed for this weaker statement. Actual compiler log has two harmless unused-change warnings at lines125 and129; it is not empty.
- `counterexample/SemanticStarObstruction.lean`, 58 lines, SHA256 `21df5075eda4fe8b8b9c1e938e319e95f779fc129efd7aa4b582e18adb2a7e09`: APPROVED. An idempotent AND hides a line input from structural OR reach. All posted hypotheses hold, but the semantic two-line OR has structural orIn={2}, and the circuit is not read1. The posted gate bound is separately verified true.
- `toolchain_setup/FeatureCover.v2.checked.lean`, 155 lines, SHA256 `e2525c43620cde4cc540c67578e9e1d60070faf40653f87703f3654cf652c02b`: APPROVED. Monotone feature factorization gives a separating feature for each edge by comparing a singleton with all nonneighbors. Feature monotonicity forces singleton-support inclusion in a neighborhood; C4-freeness then gives one covering vertex per useful feature. The circuit-to-feature factorization is an explicit hypothesis, not proved here. Matching validation has exit0 and empty stdout/stderr.
- `sat_strategy/MergeCharge.checked.lean`, 72 lines, SHA256 `5303cac24da588d680e36ab231ed0d41af30975759c20ff5e6ca000054368e77`: APPROVED. Each label merge decreases image cardinality by at most one; an initially injective set made monochromatic by k merges has at most k+1 elements. The connectivity premise is explicit. Matching saved compiler log is empty; producer reports exit0.
- `reduction_strategy/PureOrAbsorptionChecked.lean`, 53 lines, SHA256 `f69006ad1f6e077e95c137b7707a697bda4101b95f93482fb516278cd9ba460d`: APPROVED. For increasing Boolean functions, an AND below an OR of a finite variable set forces one operand below that OR, using the maximal assignment avoiding that set. Equality forces one operand equal to the OR. No circuit rewrite or size bound asserted. Matching recorded exit0 clean.
- `counterexample/UnusedStarObstruction.lean`, 84 lines, SHA256 `6f78ba0de7d10c296a9193fff96533c2f5062ecb3b3fe3dbdcc4c6628fead572`: APPROVED. Five-gate AO2 realization of a three-edge path satisfies all posted hypotheses. The first edge only has a semantic star witness at the unused final OR. Bounds and not-read1 status are checked; this is not a refutation. Matching status records exit0, empty log.

All six sources use only PEqualNP.Defs, proper L_meta_4970_aux namespaces, no forbidden proof escapes, no string literals, no disallowed attributes, and no resource options. Independent source review only; no redundant compilation was run. None states the full posted theorem.
