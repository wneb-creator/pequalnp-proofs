# Independent review: two-prefix projected lower bound

UTC: 2026-11-25T16:07:04.002183+00:00
Verdict: PASS as a checked dependency helper with explicit retained-root hypotheses. This is not an exhaustive prefix classification or a proof of L-meta-1884.

Source: `results/orch1884/lemmas/TwoPrefixFloor.lean`
SHA256: `f5b9446fe3030cacb95d432411c73fa580663b61ec20210599cf998a72778cf8`
Size: 5772 bytes; 135 lines.
Author reports Lean session94418 exit0. Complete two-prefix-floor.stdout and .stderr are independently verified empty.

The generic suffix_sixteen theorem assumes a signed Live computation whose roots are raw pins, a supplied OR of two pins, or r. It explicitly requires both pin v and r to be retained, r distinct from pin v, and r to become zero under the v=false projection. The initial list is made without duplicates before projection. Its two named roots each contribute a constant charge; the supplied OR is rebuilt from projected pins using one Reach step. The checked nine-variable signed binary floor is fifteen. The projection inequality therefore yields 15 + 2 - 1 <= k, namely sixteen suffix gates. No zero-cost rebuild or implicit root-retention claim is used.

For r = pin v AND (pin a OR pin b), with v distinct from a and b, the finite witness chooses a neighbor t of v outside {a,b}. The target changes between {t} and {t,v}, while the supplied OR, r, and every other raw pin stay fixed. Live-row separation forces pin v to remain live. I independently checked all 810 allowed ordered triples, including a=b, against the supplied neighbor masks and the certificate bit positions. The projection kills r, so the generic lemma gives eighteen gates after adding the two assumed prefix operations. r retention and r != pin v remain explicit hypotheses in the exported theorem.

The source does not prove every second gate has this form, does not prove r is retained in every minimal circuit, and does not formalize the separate Python classification of 600 surviving prefixes. Those must not be inferred from the theorem name or from the successful compilation.

Import Binary17 is a dependency-test import. The actual dependency source is the previously checked Binary17 certificate, SHA256824549cea61a489c8821209214cf8d631ef13ac9741611f3c21caf9135c72bcd. A final single-file submission would have to include its required definitions and recompile with allowed imports only. All new declarations lie in PEqualNP.Outside.L_meta_1884.TwoPrefixFloor. Options are scoped maxRecDepth/maxHeartbeats limits; no sorry, axiom, native_decide, forbidden namespace substring, quote, attribute, unsafe/meta declaration, or observed credential material occurs. The reviewer did not author this helper.
