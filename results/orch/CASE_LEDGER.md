# Canonical equality-case ledger

Updated 2026-11-25 13:42 UTC. All sets use the accepted edgeList labeling; point labels agree with the posted cyclic labeling and line labels are negated modulo seven. The full target remains open. The listed zero-surplus bounds alone do not rule out a quiet edge with two eligible endpoints.

| Eligible inputs | Canonical ineligible set | Complete no-double-quiet result | Current component |
|---|---|---|---|
| 7 | {0,1,2,3,4,5,6} | Standalone compiled | Unique-reader chains |
| 8 | {0,1,2,3,4,5} | Standalone compiled | Saturated carrier count and linearity |
| 9 | {0,1,2,3,4} | Standalone compiled ordinary impossibility | Finite residual masks, protected inputs, and sharp cofactor count |
| 9 | {0,1,2,5,11} | Standalone compiled ordinary impossibility | All one- and two-missing patterns excluded; compact standalone recheck pending |
| 10 | {0,1,2,3} | Open; three missing-mask subcases excluded standalone | Missing neighborhoods{4,5,6}+q impossible for q in{0,1,3}; q2 missing{2,4,5,6}/Bplus≤13 excluded in unconditional cached composition; full standalone assembly pending. Bplus14/Bzero0 remains; Bplus at least13; Bzero at most1 |
| 10 | {0,1,2,5} | Standalone compiled ordinary impossibility | Seven-mask family obstruction and sharp support counting |
| 10 | {0,1,2,11} | Open | Standalone Bplus at least13; Bzero at most1 by analytic cofactor bound |
| 10 | {0,1,11,12} | Open | Bplus at least13; Bzero at most1 |
| 11 | {0,1,2} | Open | Bzero=0 |
| 11 | {0,1,3} | Open | Bzero=0 from strengthened cofactor loss |
| 11 | {0,1,11} | Open | Bplus at least13; Bzero at most1 |
| 12 | {0,1} | Open | Bzero=0 |
| 12 | {0,9} | Open | Bzero=0 |
| 13 | {0} | Open | Bzero=0 |
| 14 | empty | Open | Bzero=0; exactly two consuming positions per label; every AND output has empty singleton support |

Additional cross-case result: if all seven line-neighborhood masks occur, the new false-wire surplus argument forces every point to be ineligible at27 gates and hence rules out double quiet. The standalone build and independent composition review passed.

Integration: the preferred conditional exact-statement bridge passes standalone compilation and independent review. It trims after the actual output and deletes only zero-fanout internal gates, transporting both traces through an injective wire renaming; no ordinary lower-bound/minimality premise is needed. Cyclic relabeling and canonicalization are explicit. The universal/canonical no-double-quiet theorem remains an explicit hypothesis.

New checked auxiliary results: every branch has its singleton-label value on maximal negative assignments when total surplus is at most the eligible count. The stronger K4 bound (surplus at most7 permits at most two eligible original vertices) passed both cached and standalone compilation with independent composition review. Neither alone closes the remaining Fano cases.

New generic standalone tools: the cofactor cost is at least9 when three free K4 original labels were eligible; single-reader agreement and consumption blocking control insertions after a consuming gate; support-mask closure transfers finite constructibility certificates to actual circuit supports. These tools retain their explicit hypotheses and do not close the remaining canonical cases by themselves. The protected-cone K4 and cofactor protection-transport results are cached-checked components at this freeze, with separate standalone builds pending.

Checkpoint1300: the protected-cone K4 bound and generic cofactor protection transport now have successful standalone builds and independent final-source reviews. The supported-eight lower wrapper and mixed-p9 upper wrapper are cached-checked only at this freeze. Mixed-p9 predicate transfer and the q2 finite-mask interface are standalone checked, while their finite contradiction and actual-case compositions remain separate. The prior quiet compact search ended UNKNOWN; the reviewed nine-free/topological quiet variant is active with no outcome claim.

Checkpoint1320: the complete supported-eight lower wrapper is now standalone checked. The normalized mixed-p9 two-missing composition is cached checked with an explicit finite certificate; no unconditional mixed-p9 case is claimed yet. The line-q2 residual obstruction now has a short standalone analytic proof, while the actual-circuit family hypothesis remains open in the checked cached transfer. The old exhaustive residual job was superseded and stopped143. Nine-free SAT completed UNKNOWN; the reviewed partition successor remains active.

Finite-success addendum: the full mixed-p9 finite certificate now passes permitted-import Lean and independent review. Its exact circuit instantiation and standalone assembly are the next step; this ledger does not yet mark the mixed-p9 case complete.

Checkpoint1335: the mixed-p9 two-missing theorem is unconditional in the checked cached composition and covers every two-element missing subset of{0,1,2,5}; its standalone recheck is still pending. The one-missing case remains separate. The q2 analytic backend and actual mask-family transfer now both pass full standalone builds; the complete finite certificate artifact has separate successful import/axiom validation, with original wrapper exit unavailable and runtime above30minutes. The final combined q2 cache is being integrated, so no full canonical row is newly marked closed here. No27-gate quiet witness or full target refutation is claimed.

Checkpoint1348 (2026-11-25T13:47:49.638632+00:00): complete q2 cached subcase theorem now has no finite-certificate premise, exit0, independent review and axiom audit. The new structural off-route and empty-opposite lemmas retain their stated circuit hypotheses. Full target remains open.

Checkpoint1353 (2026-11-25T13:53:22.171769+00:00): all mixed-p9 two-missing cases now have full standalone exit0 and exact composition review. Shared-slot productivity is also standalone checked. One-missing mixed-p9 and the full target remain open. Combined q2 exact-subcase standalone is actively building; no success is claimed.

Checkpoint1403 (2026-11-25T14:03:19.293067+00:00): full mixed-p9 case closed in cached Lean with independent review; full standalone pending. The combined q2 standalone had a resource failure134; independently reviewed pruning candidate is under preliminary checking, so its previous cached result is the strongest complete combined result. Public reduction quota is full.

Checkpoint1416 (2026-11-25T14:17:28.180078+00:00): actual Fano nonedge first-filter is standalone checked. Generic unordered consumer-chain cut/edge-survival is cached checked; explicit hypotheses remain. Corrected q2 standalone is active after a parser-only failed preliminary run. No further canonical row or posted target is newly closed.

Checkpoint1425 (2026-11-25T14:26:31.450653+00:00): unordered consumer-chain cut is now standalone checked; full-star chain identity and separate11-gate C6 obstruction are cached checked with explicit hypotheses. The global Fano restriction bridge and remaining canonical cases are still open. The second local witness search endedUNKNOWN; final strengthened search is active.

Checkpoint1430 (2026-11-25T14:33:43.655113+00:00): full mixed-p9 ordinary impossibility standalone passed; compact variant active. SeparateC6 obstruction is standalone checked. No further whole Fano case or target conclusion follows from the conditional surgery/filter packages. External PR15206 contains the unfinished namedpartial and was refused by intake; correction/withdrawal is prepared.
