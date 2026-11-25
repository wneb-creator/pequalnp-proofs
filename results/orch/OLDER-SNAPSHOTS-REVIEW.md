# Older checked research snapshots

These files are preserved intermediate research results, not proof-PR submissions. They do not contain the posted L-meta-9811 theorem. No new global lower bound is claimed.

| Snapshot | Lines | SHA256 | Saved build log |
|---|---:|---|---|
| AndSevenCompiler.lean | 1096 | a06716e1707e873f062c5790c92ada45e3e59c8b3af8162690d637b1732fc1bc | andseven-compiler-build.log |
| AndSevenRoot.lean | 1139 | 0641270b97343fa08db59e520f212d453bfa3cd34b8f2736125987f0f59e2d90 | andseven-root-build.log |
| DirtyCone.lean | 597 | 7f4f737013b678af735b7e9a86d0c1a55cc694b3a3f8941edfcde8cf2385f63c | dirty-cone-build.log |
| DirtyEntry.lean | 437 | fe2eb63fed995457268229ac464eec79d23a6a3cc005cbc662556c6e54184b4d | dirty-entry-build.log |
| DirtyLastEntry.lean | 689 | aa117bab02e8b7a589b333738fd58db91cc9bb0dc6245cd53bb59698104e9040 | dirty-last-entry-build.log |
| DirtyReader.lean | 323 | a78766620078d05323e17abe7a27665c752682ad243062ac711232d9f2d9760d | dirty-reader-build.log |
| DirtyReaderChain.lean | 373 | 8ca50ea8f5d88a48c128ad7862917244d4817674acf09ed51b171841f9531621 | dirty-reader-chain-build.log |
| DirtySoleReader.lean | 789 | e5b8809a394e9c4fe6c27b82215bbb725a2b58d00eca70222c29529f57473794 | dirty-sole-reader-build.log |

All six Dirty snapshots are exact prefixes of the independently reviewed TopSide.lean after removing their final namespace closure. AndSevenCompiler.lean is an exact prefix of AndSevenRoot.lean. The latter differs from the already reviewed AndSevenRootFormat.lean only by helper theorem-to-lemma keywords and the compiler declaration namespace wrapper. Their semantic content is therefore covered by the prior independent reviews. All eight saved build logs contain warnings only (five for each AND compiler snapshot, eight for the early Dirty snapshots, nine for DirtySoleReader); author-recorded compilations exited 0.

The two AND compiler snapshots retain copied helper `theorem` declarations and a fully qualified compiler theorem outside the allowed helper namespace. The source guard rejects that layout; use AndSevenRootFormat.lean as the later formatted version. Their custom compiler state structure also needs the repository manual-reader path if included in a future proof submission. None of these eight current snapshots contains `_root_` or a string literal. The six Dirty snapshots trigger only the expected absent-final-theorem guard messages. None is individually ready for a proof PR.

Research-note validation: BLOCKING-CUTS.md accurately lists conditional local restrictions from BlockingAll.lean, including arbitrary NOT gates elsewhere and the explicit output/sole-reader conditions. blocking-validation.json matches all five source hashes, byte/line counts, complete logs, warning counts, and the independently reviewed conclusions.

BOUNDARY-SEARCH.md keeps the checked global lower bound at 20 and the posted target at 25. Independent finite checks confirm maximal independent-set sizes {7:2,6:4,5:26,4:7}, C0=10, C1=2, and 39 neighborhood unions. The stated real ranks 38 and 39 follow from independence of distinct squarefree monomials after complementing right-side inputs. These measures are explicitly not offered as a 25-gate circuit proof. Bibliographic read claims remain the author’s research record; no cited overhead theorem is used as a no-cost NOT elimination.

six-three-restrictions.json was independently recomputed: the graph has four automorphisms; its 12 disjoint orbit records cover exactly all 37 six-center sets leaving three edges. Every residual edge index, nonzero degree sequence, and listed reusable partner support matches. This is finite structural data, not a circuit replacement theorem.

Independent review: PASS for preservation as research snapshots.
