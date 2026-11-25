# Upstream refresh 002: accepted-library census

Compared old upstream `cce4f255eeb0d63e821fade548e6bf41ae3d6443` to new upstream `d7dd149881faedf1819d7ca0ca51130327f5a9bb`. All182 listed Outside files were read with `git show` at the exact new commit; no checkout or branch modification was performed. `files.txt`, full main-theorem headers, selected headers, and blob hashes in `metadata.json` preserve the census without duplicating all third-party Lean sources.

## Main useful finding: L_meta_1898

Source: `lean/PEqualNP/Outside/L_meta_1898.lean` at the new commit; blob `1bacdbebeb00aa4a6cf261859953e33ea00d8315`;7334lines.

The theorem proves **at least13 AND gates** for any `Monotone2` circuit that:

1. accepts every one of the52 incidence-edge pair inputs; and
2. rejects a specified family of closed, non-pencil maximal-independent inputs, represented by a point subset P and all lines avoiding P.

Full semantics for the PG(2,3) incidence graph implies both testing hypotheses. There is no leastness, all-clean, dirty-gate-count, or AND-separation assumption. Thus it supplies an unconditional AND-count lower bound for any circuit computing the posted plane function.

It does **not** establish OR>=51, total size>=65, or the no-double-trace conclusion. Equality13 is not classified: the final contradiction only analyzes compressed AND-circuit sizes11 and12.

The internal `pg3StrongBounds` theorem (line2019) gives, for a stripped AND-count circuit D with disjoint variable sets at each AND input:

- `D.outVars = empty`, `11 <= D.size`;
- each input hits at most `D.size - 9` AND gates;
- a nonincident point/line pair jointly hits at most `D.size - 7` gates;
- a distinct same-side pair jointly hits at most `D.size - 6` gates;
- fixed-input cofactor lower bounds6 for same-side pairs and8 for nonincident mixed pairs.

At size13 these are degree<=4, nonincident mixed union<=6, and same-side union<=7. The stripping construction preserves AND count and semantics and makes singleton inputs false at all AND gates; it does not claim to preserve OR count or the original directional traces. No equality-rigidity, pair-clean, pure-cover, or double-trace=>14 theorem was found in this file. Copying the whole7334-line result is not yet justified by a complete route to our gap.

## Other relevant new results

- L1880: under girth>=5, least TopForm, at leasttwo dirty AND gates, and no dirty gate in another dirty gate cone, bounds Ustar by a universal constant times(size+1). This is a coarse bound, not a51-OR budget.
- L4913: all AND gates BelowF imply SharedBlockCost at the circuit size.
- L4915: NoFourCycle converts SharedBlockCost into ordinary BicliqueBlockCost. The preceding all-clean hypothesis remains necessary in the available bridge.
- L6963: full plane semantics implies rejection of independent inputs; a short semantic consequence, not a circuit lower bound.
- Other new generic circuit results examined concern restriction, construction, finite encoding, or unrelated small graphs. No new generic dirty-AND OR>=E-1 bound or face56 bound was found.

## L-meta-2602 status in fetched source

`L_meta_2602.lean` is absent from the exact new upstream commit. Commit-message history matching2602 contains only the three earlier reductions (full output in `upstream-2602-history.log`). No direct accepted proof or refutation was identified in this182-file refresh. This is repository status only; no desk request was made by this agent.

Research paused when the root reported lease HTTP410, pending root preservation and reacquisition.
