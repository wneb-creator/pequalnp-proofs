# Independent sensitivity and minimality review

Verdict: PASS for the partial helper checkpoint. The general L-meta-3451 normalization theorem remains unproved.

Frozen source: results/orch/lemmas/global_sensitive_min_fragment.lean, 119 lines, SHA-256 d75fb4430943629662b9020989cbf26bc838fa0bc137c77cdff503f4b1c55ea3. Verification wrapper: results/orch/lemmas/global_sensitive_min.lean, 121 lines, SHA-256 be5ad99210e18c794ce85959f25750923c88555139db2b6d50f4322d2e4a1259. Complete global-sensitive-min-001 stdout and stderr files are empty; compilation success was reported by the compiling agent.

The first Nat.find minimizes gate count among all valid monotone backward-reading circuits computing the relation. The second minimizes AND count among exactly that gate count. Thus the returned size bound is globally minimal, not just minimal within the starting budget. Replacing a selected AND with an empty OR preserves gate count, Monotone2, and ReadsBack, and strictly decreases AND count. All outputs decrease pointwise. If the selected gate had no positive edge whose global output became false, every positive edge would remain accepted; monotonicity then preserves every positive input and downward comparison excludes new false positives. This contradicts the second minimum.

The resulting conclusion is positive-edge sensitivity of every AND in a minimum-size representative. It is not singleton or nonedge cleanliness. No C4-free assumption is needed. The fragment contains only declarations under PEqualNP.Outside.L_meta_3451_aux.Prune, has no imports or forbidden syntax, and introduces no axiom or unproved hypothesis. The wrapper imports the already checked main module and is retained only as an experimental artifact.

Public metadata was independently checked at this checkpoint. posted-gap.json has only public feed data and identifies L-meta-3451; posted-statement.txt exactly matches its statement after removing the terminal newline. Their SHA-256 values are respectively 6f9ae32e2e215c9cb033ffe38d21b887b1576963ce1a971cdbe4476fc89173f3 and fb33b174a0db896523ef39937cb9e55606818500a6ba176046ea1d19a15aac53. NOTES.md at SHA-256 46a6fe037f3a9455dfc7d4c605af53291e6fb2a1eeac6568753e31084090c60e accurately distinguishes computational evidence, partial Lean proofs, and official checker status. These public files contain no credentials or live lease identifiers.

Reviewer: status_review. The proof sources were not modified. Exact merged main-file review remains a separate check.
