# L-meta-2592 repository reconnaissance

Task assigned 2026-11-25. Read-only repository inspection; no build performed and no tracked file modified.

## Semantics and statement

The gap concerns every <=19-gate circuit on ten inputs which contains at least one NOT, regardless of whether that NOT affects the output. `FanInTwo` in `lean/PEqualNP/Defs/MetaComplexity.lean:27` allows exactly AND/OR/NOT and at most two listed inputs. All gates count. `Circuit.wires` is a left fold appending one result; missing/future wire reads are false. Empty AND and empty NOT compute true. NOT ignores its second listed operand. No immediate semantic flaw or cheap counterexample was found.

The Petersen graph uses the outer 5-cycle, matching spokes, and inner 5-star. Fifteen edge conjunctions are ORed. `L_meta_1755.lean` contains a checked explicit monotone circuit with 20 gates, confirming that known upper bound with repository evidence.

## Reduction capacity

The lease response says `reductions_live: 3`. All three cuts are already on main:

- `R_meta_2592_271`: binary-floor bound `15 + notCount C <= C.size`, plus rejection for 1–4 NOT gates.
- `R_meta_2592_318`: factor at the last NOT into arbitrary prefix P and monotone suffix Q, then reject a separator with P.size+Q.size<=18.
- `R_meta_2592_408`: normalize backward reads/NOT operands/output and prove the lower bound for normalized circuits (or a strictly shorter NOT-free circuit).

A fourth reduction cannot be presumed admissible. The generic last-NOT factorization appears true, including empty/missing input NOTs: choose prefix output invalid when needed, so its eval is false. None of these reductions itself supplies the substantive lower bound.

## Concrete existing components worth reusing

Only PEqualNP.Defs and Mathlib may be imported for this gap, so outside proofs must be copied/adapted into the one submitted file rather than imported.

- `L_meta_4725.lean` (142188 bytes) proves the EXACT first hypothesis of R_meta_2592_271: `15 + PEqualNP.NotBracket.notCount C <= C.size` for every FanInTwo circuit computing the Petersen edge function. It contains a generic normalization/minimal-circuit/dependency architecture.
- `L_meta_6581.lean` (279990 bytes, 4555 lines) proves the stronger lower bound of 16 non-NOT gates. Its only import is PEqualNP.Defs. It contains a finite signed-circuit certificate, counting binary gates with free complementation. This reduces a hypothetical <=19-gate counterexample to at most three NOTs. `Extended.realize`, `atLeastSixteen`, and the final theorem are the relevant interface. The nine-variable root certificate proves at least 15 binary gates; restriction gives the tenth-variable charge. The current certificate does not reach the desired 19 binary gates needed to finish from one NOT.
- `L_meta_5236.lean` rejects a <=18-gate suffix given the initial nonedge OR x0||x2, with 3–4 remaining NOT gates and backward-read/output assumptions.
- `L_meta_5238.lean` rejects the analogous suffix with >=5 NOTs.
- `L_meta_6194.lean` restates the 15 binary-gate lower bound as countP over non-NOT operations.
- `L_meta_9037.lean` rejects circuits whose output is an original input wire (easy partial lemma).
- `L_meta_4332.lean` rejects all <=15-gate wires and their complements on the restriction x9=false.
- `L_meta_9818.lean` proves an unrestricted size>=17 bound for the ten-variable graph obtained by removing the adjacent edges (0,1),(1,2). This may help a restriction/elimination argument, but it is not a direct input restriction of the Petersen function.

Most large related files are about the nine-input vertex-deleted graph, not the full graph. `L_meta_7820.lean` and `L_meta_8551.lean` give 13 binary-gate floors on that graph; `L_meta_8035.lean` rules out its 15-gate monotone circuits. Beware confusing these with ten-input Petersen claims.

## Reusable decomposition architecture

`R_meta_651_1.lean` gives an explicit automorphism reduction of the first gate to five cases: unary, edge AND, edge OR, nonedge AND, nonedge OR. Two permutations generate enough ordered-pair orbits; finite coverage is proved by decide. The suffix receives the first gate value as an eleventh input, so no wire-index rewrites are needed.

`R_meta_2590_932.lean` gives a semantic wire-list trace model with constants supplied free, then removes duplicate wires and nonedge ANDs from a shortest monotone circuit. This can help monotone normalization but cannot be transferred through NOTs without additional arguments.

`R_meta_2590_1.lean` supplies the 30 extremal rows (15 edges and 15 maximal independent sets). Those suffice to verify a monotone circuit, but do NOT suffice for a circuit with NOTs without a separate monotonicity proof.

## Saved census artifacts

`petersen-files.txt` lists 745 matching outside files; 505 are L files. `petersen-ten-statements.txt` extracts 23 relevant ten-input final declarations. `petersen-not-final-statements.txt` extracts 18 final statements mentioning NOT counts/last-NOT decomposition. A few printed theorem types containing local `:=` bindings may be truncated by the extraction script; the source file remains authoritative.

## Independent early-checkpoint review

Reviewed current `results/orch/lemmas/Partial.lean` (108 lines, 3878 bytes) and `LastNot.lean` (78 lines, 3242 bytes). Content review PASS; compilation remains pending.

Finite graph assertions are consistent: triangle/square freedom, independence number four, minimum vertex cover six, and every input is essential. The explicit 20-gate circuit is a star cover centered at 1,3,4,5,6,7; its six stars account for all fifteen edges, and its nine local ORs, six ANDs, and five final ORs total twenty gates.

The last-NOT cut correctly retains arbitrary circuit output and deals with an empty-input NOT by pointing the prefix output at `n + pre.length`, immediately outside its wires, giving false before negation. Suffix gates are AND/OR because the selected NOT is the last one. Prefix/suffix gate counts sum to original size minus one.

No forbidden `_root_`, double quotes, attributes, sorry, axioms, or native_decide occur in these files. Imports are allowed; maxRecDepth and maxHeartbeats are scoped as required. Both files are plain text, non-executable, and not symlinks. Concatenating requires removing the second import block. Helpers do not establish the posted L-meta-2592 theorem, so this is a preservation checkpoint and cannot be opened as a proof PR.

## Complete-route search update

No complete route from existing final theorems was found. A broader census of final ten-input statements with a 19/20 bound found only known upper bounds, a construction implication, and an irrelevant contradictory-NOT premise lemma (`L_meta_8021`). The strongest general copied component remains L_meta_6581's sixteen non-NOT gates. Hypothetical circuits with one, two, or three NOTs remain; first-nonedge-OR and at least three remaining NOTs is closed by L_meta_5236. Other first-gate/low-NOT cases are not closed by the examined final declarations.

L_meta_5367 supplies a useful first-NOT cofactor bound: when given x0 and NOT x0 as inputs, the suffix needs at least 15 plus the number of gates effectively reading either of those two wires. It is around 7200 lines and not itself a contradiction for an 18-gate suffix (one to three such readers remain possible).

## Geometry support for stronger binary bound

Generated `results/orch/lemmas/Automorphisms.lean`, a 101-line insertion snippet under namespace Geometry, for insertion inside the copied L_meta_6581/Binary17 namespace. It supplies explicit automorphisms, projection tables, and first-binary isolation witnesses. Interfaces were coordinated directly with lower_bound.

Python validation passed all 1024 target rows, all 5120 target projection rows, and all 360 distinct-operand signed binary witness cases. The actual Extended.pins row-bit positions are `[9,7,5,8,6,4,2,0,3,1]`; an initially suggested different ordering failed the target comparison and was corrected before data generation. Lean checking remains pending.

The supplied-gate projection lemma shows that restricting its first operand false sends the gate to zero for d=0,2 and to the other pin for d=1,3. The witness pairs show the original first operand remains necessary even when the supplied signed binary value is available. In a peeled Live.binary suffix, both the supplied gate and that first pin belong to the live bank. Therefore d=0,2 can potentially charge TWO constants to projection mass, improving the original floor to eighteen binary gates; d=3 can swap operands to d=2. First-OR is the remaining one-charge case.

## Stronger-bound census (second independent pass)

Scanned the current outside L files using bounded filename selection. 626 files mention countP/notCount/nonNOT/binary-floor terms. Sixteen final declarations also contain a numeral 17–20; none states a general seventeen/eighteen binary-gate lower bound for ten-input Petersen. A separate source-wide search for `atLeastSeventeen`, stronger Lower certificates, and explicit 17/18/19 inequalities found 22 files and 36 matching lines; relevant-looking larger bounds concern incidence graphs with 26 or 42 variables, not Petersen. No existing checked result closes the remaining first-OR one/two-NOT cases.

New useful wrappers found: L_meta_7389 proves the normalization hypothesis in R_meta_2592_408; L_meta_6198 supplies cofactor gate deletion for a first nonedge OR; L_meta_7312 proves a second NOT is needed when a first-NOT suffix never reads the positive original pin; L_meta_7314 removes degenerate first-NOT configurations. None is a final nineteen-gate exclusion.

Complete search artifacts are retained in `/tmp/oec/pequalnp-pilot-103/count-target-candidates.txt`, `strong-floor-lines.txt`, and `ten-not-final-candidates.txt`. The signed certificate's mass counts constants only, not duplicate projected roots; a generic duplicate charge would be false for signed mux-style circuits, so a first-OR improvement needs a target-specific argument.

## Nine-variable cofactor NOT census

No checked result was found excluding a sixteen-gate circuit with one NOT, or a seventeen-gate circuit with two NOTs, for the twelve-edge Petersen vertex deletion. A census of 127 final declarations with the relevant size range found total-size floors of sixteen, not seventeen. Many impose first-gate conditions, exactly one/two NOTs, or special read counts; these still only conclude sixteen. L_meta_10996 is a different eleven-edge graph on nine vertices and proves only a total-size floor of fifteen; nearby 10994/10998 are also different graphs.

The cofactor has a sixteen-gate monotone upper bound: choose minimum vertex cover (0,1,3,7,8), build its five stars, then OR the outputs. Python checked all 512 rows. Circuit data is saved in `/tmp/oec/pequalnp-pilot-103/nine-mono-upper.txt`. Consequently the desired strengthening needs a positive-NOT exclusion, not a blanket total-size lower bound of seventeen. The exact missing SAT target is fifteen binary gates plus one NOT (sixteen total), or fifteen binary gates plus two NOTs (seventeen total).

Updated 2026-11-25T14:40:01.377488+00:00


## Optimal monotone cofactor route: deletion findings

- `L_meta_2668.lean` (460 lines, 21,338 bytes) proves a useful generic minimality fact. For any minimum monotone circuit computing a graph edge function, every AND gate accepts an actual edge-pair on which bypassing that gate to an invalid wire (constant false) destroys the output. Its internal `lost_edge` at line 395 actually applies to every gate, and the AND assumption `_hand` in internal `main` at line 432 is unused. Hence every gate must be productive on some true edge-pair, without a star normal form.
- Equivalent semantic proof: zeroing an intermediate that is false on every actual edge-pair lowers all subsequent values, preserves all true edge-pair outputs, and therefore preserves the entire quadratic monotone graph function. Deleting that gate contradicts minimum size. For a size-16 minimum nine-variable cofactor circuit this rules out pure nonedge conjunctions and pure independent-triple conjunctions.
- `R_meta_2590_932.lean` already checks a trace-level implementation: `MaskRel` at line 256, `replace_trace` at 271, `mask_target` at 297, `delete_nonedge` at 337–350. It is specialized there to a raw nonedge AND, but its preservation argument applies to any wire zero on all edge pairs.
- Crucial limitation: a wire with an independent-triple minterm may also accept useful edge pairs. Lower-bound agent confirms the remaining reader operand g is only known to vanish on singleton and independent-pair rows; it may accept useful edge pairs. Thus the generic deletion theorem does not eliminate the remaining mixed case.
- `L_meta_4849.lean` refutes the general assertion that all AND gates in every minimum monotone circuit for a triangle-free, C4-free graph reject every nonedge pair. Its checked counterexample has eight inputs, eleven gates, and graph edges [(0,4),(0,6),(1,5),(1,6),(1,7),(2,6),(3,7),(4,7)]. This cautions against imposing a clean star normal form; it does not itself refute a graph-specific nine-variable cofactor claim.
- Conditional bounds `L_meta_7241` and `L_meta_8933` do not close the remaining case: the first assumes every AND rejects all nonedge pairs, while the second has a conditional restriction on non-below-target AND gates accepting two multiply-read edges. Neither supplies a strict seventeen-gate bound for the mixed useful-edge plus independent-triple case.
- Remaining possible route is a graph-specific classification of minimum16 circuits, or stronger semantic structure of g forced by the surrounding two-reader NOT circuit. No such checked theorem was found in the bounded existing-source census.

Proof investigation paused at parent request following lease HTTP410. No desk requests, git actions, or further proof edits by this agent.
