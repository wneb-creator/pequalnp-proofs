# Independent reduction/status audit

All three existing reductions have their structural/counting premise proved in accepted repository files:

- R_meta_2592_271.binaryFloor: L_meta_4725, 3224 lines, proves exactly `15 + NotBracket.notCount C ≤ C.size` for the Petersen edge function. Thus any counterexample with size ≤19 has 1–4 NOT gates. Its branch-count proof is generic but long.
- R_meta_2592_408.normalize: L_meta_7389, roughly 290 lines, proves the exact normalization premise: remove invalid reads and surplus NOT inputs, trim to last output, preserve a NOT or strictly lower size.
- R_meta_2592_318.cutLast: L_meta_8295, roughly 80 lines, proves exact last-NOT cut into FanInTwo prefix P and monotone suffix Q with sizes summing to C.size−1.

The remaining premises are respectively the genuinely hard few-NOT bound, normalized bound, and last-NOT separator. L_meta_8021 superficially resembles few-NOT but additionally assumes every gate is NOT-free; it merely proves contradiction with notCount≥1 and cannot help.

Other reusable results:

- L_meta_2826 (201 lines): translate FanInTwo to signed-AND BinaryCircuit, absorbing NOTs into wire polarity; translated size plus NOT count is at most original size.
- L_meta_7227 (266 lines): refined translation tracking a set of at most notCount complemented wires. Could reduce finite search to 15–18 signed binary gates with only 1–4 marked complement wires.
- L_meta_5236 (4560 lines): with the extra free input x0∨x2, any circuit computing Petersen needs ≥16 non-NOT gates; statement rules out size≤18 with 3–4 NOTs. Stronger normalization via first gate may eliminate some cases.
- L_meta_5238: same extra-input situation, excludes ≥5 NOTs using the generic 15 non-NOT floor.

No definition loophole found: FanInTwo restricts operations to AND/OR/NOT; invalid or forward wire reads are constant false; empty AND and NOT are true, empty OR is false; NOT ignores all but its first input. Unused gates still count. Existing normalization handles these cases.

Every reused proof must be copied/reproved into the single named file because only PEqualNP.Defs (plus Mathlib) is allowed, not Outside modules. Existing files contain multiple `theorem` declarations and arbitrary namespaces; final checker format should be independently inspected after merging.

## Signed-first-gate route update

The checked components now establish the arbitrary pair residual bound (FewNotGeneric.pair_sixteen), and GlobalSeventeen combines it with live derivation extraction to prove 17 + notCount C <= C.size. Thus only one or two NOTs remain under a 19-gate budget.

NonOrSeed further proves a residual bound of17 for normalized first gate AND, AND-NOT, or NOT-AND. A live seed and its essential input both project to constants; if the seed is absent, the global17 live floor applies directly. The normalized OR case remains.

For an explicit physical circuit, normalized OR may arise either from an OR of positive inputs or from an AND of two negated inputs (NOR, then normalized by complement). SAT reductions must retain both possibilities.

A generic charge for duplicate projected signals is unsafe even for monotone graph functions. The P4 edge function ab OR bc OR cd is computed in4 binary gates by b AND (a OR c) OR (c AND d), which has two copies of c as formula leaves. Complete Python enumeration of the four normalized signed AND/OR gate forms found no circuit with at most3 binary gates (distinct state counts24,468,8756 at depths1,2,3). Thus this duplicate input need not imply a gate saving. Any OR-case improvement requires extra Petersen structure or a bound on explicit NOT gates.

Root suggested the one-NOT-input reader restriction: setting that input to0 removes the NOT and the effective readers of both polarities. Structural and library agents are investigating the accepted R-module in L5367 with the nine-vertex size16 lower bound.
