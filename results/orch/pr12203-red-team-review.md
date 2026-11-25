# Independent PR12203 red-team review

Verdict: PASS for the mathematical bridge and static source rules. Complete kernel replay, recursive axiom audit, and repository checker remain required. This report does not replace them or assert that the previous timeout is resolved.

Source: public PR [12203](https://github.com/open-goat/pequalnp-proofs/pull/12203), author **0xshuzo**, revision `0d2bbcdeb511ffff33552e155db3526648d8575b`. Original source SHA-256: `5bc7f362c1cf08ca49a34dea07ed4ff386f2b393efb6261efa57a20c37f10348`.

## Exact task and circuit bridge

The final theorem matches the posted L-meta-670 statement, including all nine inputs, twelve edges, and the inclusive at-most-15 gate budget. Independent Python checks verified all 512 graph truth bits, all 4,608 input-column truth bits, and all nine essential-input witness pairs. The core circuit semantics, extraction lemma, Live/Impossible predicates, and ordinary node soundness proof are unchanged from the already reviewed PR12184 source.

`twoRoots` proves the required mode split from any legal circuit of size at most 15. With no NOT gate, the extracted monotone Live run has at most 15 binary steps. If a NOT occurs, the count of non-NOT gates is strictly below total size and therefore at most 14. Free-complement normalization applies only in the latter mode. Essential-input witnesses force the extracted initial set to equal the complete nine-input set. No first-gate hypothesis, omitted input, or strict/inclusive off-by-one change is introduced. The modes are encoded by bit 10 of the forest mask: monotone mask1535 and signed mask511 share exactly the lower nine input bits. Final root equality checks use the actual complete input state.

## KW and panel path

`KWRooms` explicitly requires total, valid, unique, rectangular ownership of target-positive/target-negative row pairs. `kwTight` obtains it only from `Live false` and exact cardinality `|S|=k+1`; the width bound forces both consumed operands to be absent from the retained set. Its AND selector depends only on the negative row and its OR selector only on the positive row, preserving rectangularity. `kwWord_sound` checks the exact cardinality condition and distinct selected wires before deriving the rectangle-crossing contradiction.

`oneShare` uses the explicit budget `k≤|S|`. Both operands retained is excluded by the width bound; exactly one retained uses a tight tree and `factorKeep`; neither retained recursively expands the partition side containing the newly computed wire. The resulting SingleFactor has explicit disjointness, complete coverage, an inner KW ownership system, and an outer ownership system permitting only the named pivot exception. This argument applies to arbitrary input signals; it does not assume that those signals themselves are monotone functions.

The seven panel contradictions follow from the proved horn and parity rules. Independently evaluated all 128 Boolean membership assignments across the seven propositional panel lemmas, with no countermodel. A second review by /root/normalization checked every panel's coordinate calls, arities, and the KWRooms-to-SingleFactor proof; its evidence is in `pr12203-panels-independent.json`.

`panelCheck` checks membership of every selected wire, pairwise distinctness, and every required actual truth-table separator. `panelWord_sound` checks its budget before obtaining SingleFactor. Defaults and out-of-range packed selectors do not imply acceptance: their resulting actual rows/wires still face all these predicates. Unknown panel indices select the proved final panel, not an unchecked certificate.

## Mixed forest coverage and certificate trust

`CutRow` permits exactly two alternatives for every state index: the ordinary Boolean checker succeeds, or the identical state already has a proved Impossible predicate. `mixedCut` and all panel dispatch paths require mode=false; the signed path continues through ordinary checked tables. Dispatch tag0 uses the ordinary checker, tags1–127 use the proved KW checker, and tags128–255 use the proved panel checker. None bypasses a soundness theorem.

`mixedForest` inducts on the level. Ordinary links use only the preceding level, validated automorphisms, and bounded indices; direct KW/panel impossibility is an independent proof at the current level. `mixedRoot` checks the root index and actual state equality before transferring the bound. Joined row intervals cover every listed state. Independently matched all root level counts: monotone levels9–15 have 7,182,820,386,66,9,1 states; signed levels8–14 have 6,69,373,216,30,3,1 states. The table theorems also explicitly handle every lower empty level.

Compressed records, sorted hints, and lookup structures select candidate states/rules only. Retained rules still pass `buildRule_sound`; linked states still require valid bounds, checked automorphisms, and exact state matching. Arbitrary decoded data cannot supply an axiom or escape the ordinary or KW/panel soundness obligations.

## Format and trust checks

The actual repository `checkProofFile` and `checkFileKind` pass on the original source. Its sole import is `PEqualNP.Defs`; its 523,482 bytes leave 806 bytes below the 512KiB cap. No added axioms, proof holes, unsafe/native evaluation, strings, forbidden attributes/options, imported critical-name shadowing, or out-of-namespace helpers were found. The full theorem is written at top level with its required fully qualified name. New small structures carry ordinary propositions/proofs and introduce no trust extension.

The frozen attributed original-depth candidate has only 239 additional comment bytes, credits 0xshuzo correctly, and retains the original shared-source credits. Its independent byte/guard audit is separate from this semantic review. Full compilation and checker acceptance are still pending.

Reviewed UTC: 2026-11-25T05:22:33.559468+00:00
Reviewer: /root/status_review, with independent KW/panel review from /root/normalization.
