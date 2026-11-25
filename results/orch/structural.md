# Structural strategy notes

- R_meta_2448_263 contains a proved local `pairDirt` lemma: in a C4-free graph, a fan-in-two monotone AND gate owning two disjoint graph edges fires on a nonedge pair among their four endpoints, permitting singleton pairs. This is independent of minimality.
- Its remaining two repair hypotheses hSingle and hPair assert a size-preserving circuit transformation decreasing the count of gates owning disjoint edges, depending on whether the false positive is a singleton or a proper nonedge.
- R_meta_2448_17 instead classifies gate-owned graphs after an unproved crossing condition into double stars or C5; C5 ownership forces a singleton false positive. It then assumes an extension of a star prefix.
- L_meta_8237 (checked) proves that if any gate of a minimum monotone graph circuit is true on a singleton u, replacing that gate by u loses some graph edge disjoint from u. The proof supplies substantial deletion/replacement lemmas. This blocks the naive strategy of simply replacing a dirty singleton gate by that input.
- L_meta_2668 proves every AND gate in a minimum monotone graph circuit is critical on some edge, via eraseGate-to-false.
- A plausible broad route is a size-preserving quadratic monotone normal form, or the lower bound |E| + vertex-cover-number - 1 for graphs without C3/C4. Neither has yet been derived; dirty intermediate gates may accept nonedges filtered by later AND gates, so false positives alone do not contradict correctness.
