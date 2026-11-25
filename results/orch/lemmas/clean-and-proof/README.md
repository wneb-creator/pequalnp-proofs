# L-meta-1904 route review

Public open-PR census on 2026-11-25 returned zero entries for `1904 in:title,body` in brilliant-hq/pequalnp-proofs. The structured response is preserved as pr-census.json. Its count is below the requested 100-result limit, so this query was exhausted.

Three reductions are already live, filling the stated reduction cap:

| Cut | Accepted children | Remaining open children |
| --- | --- | --- |
| R_meta_1904_137 | L4320: safe-AND cover builder | L4316: singleton normalization; L4318: edge-plus-cover budget after normalization |
| R_meta_1904_271 | L5733: forests/cycles; L5735: minimum-cover safe upper bound | L5737: matching lower bound for the remaining girth-at-least-five graphs |
| R_meta_1904_493 | Its proof already upgrades pair safety to global safety | L5282: singleton-safe minimum circuit; L5284: pair-safe conversion |

The copied accepted sources are research references, not new proofs or locally revalidated artifacts. accepted-support.json records their exact hashes, public authors and commits; the L-source hashes were checked against the public feed. Child statements are preserved in children1904.json.

R493 already contains the useful prefix provenance argument: before the first unsafe AND, every true wire on an independent input has a singleton witness, yielding a violating set of at most two vertices. That argument does not establish the still-open singleton or pair normalization steps.

RankedMinimum.lean is a newly prepared small general selection lemma: choose an equivalent Monotone2 circuit with least size, then minimize any natural-valued secondary rank. It compiled successfully with the required PEqualNP.Defs import at -M6500/-j1, exit 0, 10.91 seconds wall and 2,877,280 KiB peak child RSS; complete logs and source hash are saved alongside it. It can support a least-number-of-bad-AND-gates argument, but does not show that this number is zero or prove the posted statement.

No full proof of L1904 has been obtained. Existing general library edge-function lower bounds requiring girth seven/nine or separated high-degree vertices do not establish the girth-five case.

A simple local operand-bypass normalization is insufficient. The independently checked UnsafeBypass.lean in ../clean-and-lower/ exhibits g=(a∨c)∧(a∨b), output=g∧(c∨d), computing the path with edges ac/ad/bc. Replacing g by either operand introduces a false positive. Replacing g by a∨bc works by distribution but requires accounting for shared upstream OR gates in the general circuit. This is a demonstrated obstruction to the attempted proof strategy, not a refutation of L1904.

DiamondRank.lean compiled with canonical PEqualNP.Defs at -M6500/-j1, exit 0 in 11.923 seconds with 2,905,448 KiB peak child RSS. It contains the frozen checked DiamondRewrite helpers from ../clean-and-lower/ and proves a new secondary-rank decrease: sum over singleton inputs of the number of active AND gates. Rewriting the three-gate primary-input diamond preserves Monotone2 and decreases this rank by exactly 1 when b≠c and the suffix never reads the changed middle wire. Full stdout/stderr and source digest are in diamond-rank.*. This excludes such an exposed diamond from a minimum-rank circuit but does not prove that every dirty circuit exposes one.

DiamondRankMinimal.lean combines the checked rank/surgery and RankedMinimum proofs, then proves that every Monotone2 circuit has an equivalent minimum-size circuit avoiding every exposed primary-input diamond satisfying b≠c, no suffix read of the changed middle wire, and an output distinct from that wire. Canonical-Defs validation passed exit 0 in 6.349 seconds, peak RSS 2,911,320 KiB, with complete diamond-rank-minimal.* logs. The theorem excludes only this explicitly described local pattern; it does not establish the full safety statement of L1904.
