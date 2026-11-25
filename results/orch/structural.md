# Structural strategy notes

- R_meta_2448_263 contains a proved local `pairDirt` lemma: in a C4-free graph, a fan-in-two monotone AND gate owning two disjoint graph edges fires on a nonedge pair among their four endpoints, permitting singleton pairs. This is independent of minimality.
- Its remaining two repair hypotheses hSingle and hPair assert a size-preserving circuit transformation decreasing the count of gates owning disjoint edges, depending on whether the false positive is a singleton or a proper nonedge.
- R_meta_2448_17 instead classifies gate-owned graphs after an unproved crossing condition into double stars or C5; C5 ownership forces a singleton false positive. It then assumes an extension of a star prefix.
- L_meta_8237 (checked) proves that if any gate of a minimum monotone graph circuit is true on a singleton u, replacing that gate by u loses some graph edge disjoint from u. The proof supplies substantial deletion/replacement lemmas. This blocks the naive strategy of simply replacing a dirty singleton gate by that input.
- L_meta_2668 proves every AND gate in a minimum monotone graph circuit is critical on some edge, via eraseGate-to-false.
- A plausible broad route is a size-preserving quadratic monotone normal form, or the lower bound |E| + vertex-cover-number - 1 for graphs without C3/C4. Neither has yet been derived; dirty intermediate gates may accept nonedges filtered by later AND gates, so false positives alone do not contradict correctness.

## Checked scratch components

- `StrongStructural.lean`: 435 lines, pinned Lean exit 0, empty log. Exposes cross_nonedge and star_of_proper_pair_sound (singleton behavior unrestricted). Adapted checked L_meta_7406 plus an explicit star conclusion.
- `DiamondFull.lean`: 202 lines, pinned Lean exit 0, empty log. Three-gate common-input OR/OR/AND block becomes two-gate AND/OR. Arbitrary prefix/suffix allowed; suffix/output may not read the two discarded OR intermediates. Saves one gate and proves the original block cannot occur in a minimum circuit under these conditions.
- `Matching.lean`: 215 lines, pinned Lean exit 0, empty log. Preserves previously computed/shared A=a OR c and B=b OR d, replaces five-gate (A AND B) AND ((a OR d) AND (b OR c)) by three-gate (a AND b) OR (c AND d). Arbitrary prefix/suffix allowed; suffix cannot read four discarded intermediates. Saves two gates.
- `KeepLeft.lean`: pinned Lean exit 0, empty log. Equal-size common-input diamond repair: retains first OR(s,a), changes second OR(s,b) to AND(a,b), changes final AND to OR(s,newAND). Only the old second-OR wire must not be read outside the block. Preserves minimality. Earlier first-OR users remain valid and unchanged.
- `InputStar-snippet.lean`: primary-input operand forces owned edges to contain that primary vertex. Combined compilation passed with empty log after a minor linter cleanup.
- `Prefix-snippet.lean`: ownership is invariant for a gate in a common circuit prefix; compiled exit 0 with empty log.
- `KeepLeftStar-snippet.lean`: compiled exit 0 with empty log; equal-size repair extends a star prefix whenever a is primary (s and b may be arbitrary earlier signals). Combined KeepLeftStar.lean builds all these components together.

## Remaining mathematical obstacle

None of these local repairs shows that an arbitrary minimum circuit with a bad ownership gate contains a repairable block. The missing step is a global structural or counting argument controlling shared dirty operands. Nonminimum C6 circuits can share both operands of a dirty AND, so no-C3/C4 alone does not forbid sharing. The singleton-overlap case yields neighborhood restrictions: along u-a-b, N(u) intersect N(a) is empty and N(u) intersect N(b) is contained in {a}. Clean direct users of shared factors may then make the dirty gate redundant, but dirty shared users can form larger components.
