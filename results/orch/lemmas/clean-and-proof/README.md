# L-meta-1904 route review

Public open-PR census on 2026-11-25 returned zero entries for `1904 in:title,body` in brilliant-hq/pequalnp-proofs. The structured response is preserved as pr-census.json. Its count is below the requested100-result limit, so this query was exhausted.

Three reductions are already live, filling the stated reduction cap:

| Cut | Accepted children | Remaining open children |
| --- | --- | --- |
| R_meta_1904_137 | L4320: safe-AND cover builder | L4316: singleton normalization; L4318: edge-plus-cover budget after normalization |
| R_meta_1904_271 | L5733: forests/cycles; L5735: minimum-cover safe upper bound | L5737: matching lower bound for the remaining girth-at-least-five graphs |
| R_meta_1904_493 | Its proof already upgrades pair safety to global safety | L5282: singleton-safe minimum circuit; L5284: pair-safe conversion |

The copied accepted sources are research references, not new proofs or locally revalidated artifacts. accepted-support.json records their exact hashes, public authors and commits; the L-source hashes were checked against the public feed. Child statements are preserved in children1904.json.

R493 already contains the useful prefix provenance argument: before the first unsafe AND, every true wire on an independent input has a singleton witness, yielding a violating set of at most two vertices. That argument does not establish the still-open singleton or pair normalization steps.

RankedMinimum.lean is a newly prepared small general selection lemma: choose an equivalent Monotone2 circuit with least size, then minimize any natural-valued secondary rank. It compiled successfully with the required PEqualNP.Defs import at -M6500/-j1, exit0, 10.91seconds wall and 2,877,280KiB peak child RSS; complete logs and source hash are saved alongside it. It can support a least-number-of-bad-AND-gates argument, but does not show that this number is zero or prove the posted statement.

No full proof of L1904 has been obtained. Existing general library edge-function lower bounds requiring girth seven/nine or separated high-degree vertices do not establish the girth-five case.
