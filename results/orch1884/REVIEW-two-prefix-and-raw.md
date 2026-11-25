# Independent review: raw-input AND as the second prefix gate

UTC: 2026-11-25T16:09:25.370731+00:00
Verdict: PASS as a checked dependency helper, with explicit retained-root and distinctness assumptions. No complete syntactic case classification or full gap theorem is claimed.

Source: `results/orch1884/lemmas/TwoPrefixAndRaw.lean`
SHA256: `5bbccfc24d022434fa96cbf75bce32a8b6897cd975ee455dd7e9a15b4301ae6c`
Size: 4372 bytes; 98 lines.
Author reports Lean session76486 exit0. Complete two-prefix-and-raw.stdout and .stderr are independently verified empty.

When an AND operand v is outside the first OR pair {a,b}, the existing checked Binary17 witness varies v while preserving the supplied raw AND and every other pin. The first OR is also fixed because its operands differ from v. Live-row separation therefore forces pin v into the suffix root set, and projection kills both that pin and the retained AND result. The reviewed suffix_sixteen theorem applies exactly.

When the AND and OR use the same pair, the new swap witness chooses a neighbor of a which is not a neighbor of b. The two assignments {t,a} and {t,b} give different Petersen values while both the OR and AND agree and all other pins agree. Thus at least one of pin a or pin b remains live. Whichever one is retained can be projected to false, killing the conjunction too. I independently verified existence and the target distinction for all ninety ordered distinct pairs using the supplied neighbor masks. The proof handles the two retained-pin branches explicitly and uses the corresponding freshness hypothesis.

Both exported conclusions are 18 <= k + 2 for the stated signed Live suffix model. They assume the conjunction is retained and distinct from the relevant raw pins; they do not prove those facts for an arbitrary syntactic circuit or classify all possible second gates. The previous AND-of-OR case and these raw-AND cases still require a separately checked integration argument before a global statement can be claimed.

Import TwoPrefixFloor is a dependency-test import. Its reviewed source hash is f5b9446fe3030cacb95d432411c73fa580663b61ec20210599cf998a72778cf8 and it in turn imports the checked Binary17 certificate. A final submission requires allowed imports and a new standalone build. All new declarations lie in PEqualNP.Outside.L_meta_1884.TwoPrefixAndRaw. Options are scoped allowed limits. No sorry, axiom, native_decide, forbidden namespace substring, quote, attribute, unsafe/meta declaration, or observed credential material occurs. The reviewer did not author this helper.
