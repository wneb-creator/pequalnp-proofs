# L-meta-1890 shared notes

Root owns fresh lease issued 2026-11-25T14:39:23.369Z. Only root desk/commit/push. Append timestamped findings under agent name.

Goal: Petersen edge function cannot be computed by <=18 fan-in-two gates from arbitrary mapped ten inputs plus free x0 AND x2. Imports allowed PEqualNP.Defs and Mathlib. Three reduction slots already occupied.

## counterexample 2026-11-25T14:40:31.908913+00:00
No semantic loophole: FanInTwo only AND/OR/NOT; sequential evaluation; future/out-of-range wires false. Identity input map maximizes available info and suffices for witness search. No installed SAT solver; preparing bounded truth-table synthesis.

## status_review — 2026-11-25 14:40:45 UTC

- L-meta-1890 has three merged reductions: R_meta_1890_1 (next-gate AND/OR/NOT), R_meta_1890_2 (empty/first gate), R_meta_1890_47 (delete a vertex, save four gates, invoke seeded nine-vertex minor bound).
- R_meta_1890_47 minorBound is already checked by L_meta_1668 (seed pair 0,2), L_meta_1669 (0,3), L_meta_1671 (0,6), and L_meta_1672 (4,6). Each gives 16 <= C.size for the nine-vertex Petersen minor with first wire equal to its seed. Files have 4287/4673/7133/7135 lines; machinery needs deduplication to fit final 512KiB cap.
- Remaining substantive hypothesis in reduction47 is eliminate: any <=18 gate seeded ten-vertex solution loses >=4 gates on some x_v=false slice. Investigating whether its child is now checked.
- L_meta_6024 (40 lines) proves empty-gates branch of reduction2. L_meta_7989 proves <=1 suffix-gate branch after next AND. L_meta_8079 only reattaches the given AND/NOT prefix to produce a <=19 gate ordinary circuit; it is not a lower bound.
- Fully paginated GitHub search for exact L-meta-1890 returned 15 matches, incomplete_results=false, no open PR. The merged main reductions are #8149, #7680, #9900. #7680 authoritative comment: ACCEPTED checker exit0 (https://github.com/open-goat/pequalnp-proofs/pull/7680#issuecomment-7140844071).

## Root 2026-11-25T14:41:38.624101+00:00
Drafted input-remapping partial in named file: any omitted vertex gives two indistinguishable observed inputs with opposite Petersen values. Hence a computing remapping must be surjective. Finite witnesses use one neighbor per vertex and avoid nonedge {0,2}; awaiting toolchain to check.

## structural_proof 2026-11-25T14:42:34.164058+00:00

The supplied nonedge conjunction can be erased semantically for a monotone suffix: set the extra input false. The resulting monotone function is <= the original and agrees on every edge-minterm, where x0 AND x2 is false, hence still computes Petersen. This does not extend immediately to NOT gates.

Existing L_meta_4566 contains generic least-circuit/first-branch/ledger machinery and proves at least 14 non-NOT gates for Petersen-minus-vertex; L_meta_6194 gives at least 15 non-NOT gates for Petersen10. These alone do not imply the needed18 seeded bound. The generic four-gate restriction required by R_meta_1890_47 is not forced by simple input-fanout counting; substantial structural casework remains.

### status_review — 2026-11-25 14:42:58 UTC: combined minor theorem found

- L_meta_7215.lean is EXACTLY minorBound of R_meta_1890_47. It already combines the four required seed pairs, using 381652 bytes / 4899 lines and only PEqualNP.Defs. This avoids deduplicating 1668/1669/1671/1672 ourselves. Re-namespace its helpers under L_meta_1890 and turn final theorem into an internal lemma; add R1890_47 transport helpers. Approximately 130KB remains for the eliminate proof.
- Public search index for token1890 identifies children7215 and7217 for the vertex-deletion reduction. There is no L_meta_7217.lean or R_meta_7217_* file; complete GitHub search for exact L-meta-7217 returned0, incomplete_results=false. Exact public child statement still being confirmed.

## counterexample 2026-11-25T14:43:19.484155+00:00
Kissat built from github.com/arminbiere/kissat in scratch; exact SAT synthesis launched with documented --time=120. Encoding supports all AND/OR/NOT circuits up to padding; rows initially every input of weight<=2 plus every independent set, adds all counterexamples to each SAT model. Search source results/orch/lemmas/counterexample/synth.py. Stochastic search has reached an 18-gate approximate circuit wrong on 12/1024 assignments; this is not a witness.

## finite_certificate 2026-11-25T14:46:32.973187+00:00
- LRAT library LinkN/LinkN2 handles NOT; Defs.LratEncoding itself is monotone-only. A seeded promise can use11input rows r+1024*(bit0 AND bit2), with1024allowed rows. Any LRAT certificate still needs copied soundness and exact encoding linkage.
- L1668 is a generic backwards live-wire proof plus kernel-checked finite tables,303022bytes. L670 and L4033 give arbitrary-circuit nine-vertex Petersen minor lower16 (523341/521569bytes).
- Implemented exploratory generator results/orch/lemmas/finite/live_search.py: full1024truth tables,225then768positive/negative row pairs,185subcube restrictions,158smallgraph lower bounds parsed from L1668. Initial60second depth2 search:51735states,16978restriction cuts,2141coverage cuts,32494open frontier. No full certificate yet.
- Tightness idea: with seeded10rootcap18, restriction x0=0 orx2=0 makes two live rootsconstant. Minor16plus2constants gives exact18, so a hypothetical circuit must achieve equality in contraction on BOTH endpoint restrictions. Noresidual<=17 follows immediately from this minor bound.

## counterexample 2026-11-25T14:46:41.885743+00:00
First SAT CEGIS solve hit120s documented wall limit: UNKNOWN, no model and no UNSAT proof. Fixed known20-gate CNF validates SAT and its circuit matches all1024assignments. Launching300s run with exploratory normal-form symmetry; failure of that run is not a lower-bound proof. Full logs under job scratch synth-18*.

### status_review — 2026-11-25 14:46:52 UTC: small formula route sources

- L_meta_531.lean (454lines,23937bytes) proves every positive de Morgan formula for a triangle-free and C4-free graph has at least |E|+|T| leaves for some vertex coverT. Petersen gives15+6=21. This is the exact useful graph pattern theorem, with only Mathlib+Defs imports. Old global private helper declarations must be wrapped under target namespace.
- L_meta_258.lean (372lines,14466bytes) proves a minimum-leaf formula for a monotone essential function contains no negative occurrence of any variable read<=2. Its proof uses only constant substitution and simplification (`sub`, lines262-293), so it can be adapted to minimum among readtwice formulas by proving each variable count does not increase. Arbitrary global minimization alone does not preserve readtwice.
- L_meta_905.lean rules out <=6-AndCountCircuit representations of Petersen with each variable bare-read at most2, but conversion from general circuits is extra work.
- PEqualNP.ReadK/ReadTwo are per-prime-implicant proof-tree read notions, not total syntactic variable occurrence counts; avoid confusing these.
- Public map:7215 status c (checked),7217 status j (conjecture), latter node hash a9ce9e12e493. Exact7217 has0GitHub PR search matches and no existing proof/reduction file.

## counterexample 2026-11-25T14:47:37.683320+00:00
Verified stochastic best18 candidate is only approximate: misses12 true assignments, each involving edge0-4 or2-7, and has no false positives. Target true on948/1024 assignments. Thus it is not a refutation. Known20-gate upper bound saved as scratch known20.json; validated all1024rows and fixed-structure CNF SAT.

## structural_proof 2026-11-25T14:47:48.781695+00:00

Draft `results/orch/lemmas/structural/SeedErase.lean` proves generic minterm-based seed deletion and applies it to any Monotone2 suffix and arbitrary remapping p. Awaiting toolchain/Defs build to test.

Counting route: a live normalized19-gate full circuit (free seed prepended) has at most binaryCount+1 <=20 raw-input incidences. If all10 variables are read at least twice, equality forces20 incidences, noNOTs, nointernalfanout, and exactlytwo leaves pervariable. Root assigned readtwiceagent to close that positiveformula case with checkedL531. AnyNOT/internalsharing forces a readonce rawvariable; difficult step is proving its companion cone can be removed after setting itfalse.

Stronger endpoint route from finite_certificate: pure9minor bound16 forces the18-gate suffix to save exactly2 gates under x0=0 andx2=0. Heuristic equality characterization: each endpoint andfree seed readonce andonlybyOR; anAND/NOT consumer would becomeconstant andforce athirddeletedgate. A consumer combining endpoint andseed is redundant since x OR(x AND y)=x andx AND(x AND y)=x AND y. This characterization is notyet formalized.

## readtwice 2026-11-25T14:49:02.056928+00:00

L_meta_531 gives positive De Morgan formula leaf lower |E|+vertex-cover, so Petersen needs at least21 leaves. Extracted proof and finite specialization in results/orch/lemmas/readtwice/FormulaLower.lean (~40KB including L7111 fanout-one unfolding), awaiting Defs build. This closes the no-sharing AND/OR binary circuit case at size19. The full-count route then forces some rawinput readonce; vertices0/2 cannot be sole-read at the seed because toggling with opposite endpointfalse leaves seedunchanged but changes a neighboring edge. Need normalized/live circuit incidence argument and readonce⇒four-gate-saving lemma.

## counterexample 2026-11-25T14:50:10.483522+00:00
After root renewal, launched600-second focused search: first gate fixed NOT(x0 AND x2), remaining17 gates AND/OR. Uses same exact1024-row validation; purpose is to explore cancellation using the nonedge seed. No witness yet.

### Status review 2026-11-25T14:51:16+00:00
- Extracted `results/orch/lemmas/status_review/RawRaw.lean` (208 lines, 9338 bytes), pending Defs build: generic lockstep from L4115 plus finite Petersen private-neighbor witnesses. Any AND/OR gate with distinct raw inputs forces both raw inputs to be read at least twice. L4115 used girth7 only to obtain girth5, so Petersen specialization valid. No absorbing-wire bulk needed.
- Generic four-gate elimination: L7085 handles two distinct AND/NOT readers; L7087 handles exactly two readers OR+NOT unless the NOT solely feeds an AND; L7089 handles that exceptional pattern and gives saving4 when an OR reader exists. Need normalized minimal circuit and nonconstant zero restriction. Seed endpoints already read by AND, so any second AND/NOT forces enough full-circuit savings for nine-vertex bound16.
- L6581 proves Petersen needs at least16 non-NOT gates (stronger than L6194 at15), 284540 bytes. L7804 yields adjacent vertices both read at most2 whenever a circuit is below edgecount+minimum vertexcover−1.

## counterexample 2026-11-25T14:52:35.858462+00:00
Stopped the less focused stochastic variant after observing it consistently left the forced NOT unused. Replaced by variant requiring the NOT to lie on the output path (600s), and exact SAT requiring exactlyone NOT of the free seed (300s). Full earlier log retained, no witness. Generic stochastic search completed1493762048mutations in600s without a witness; both generic120s and normal300s SAT runs returnedUNKNOWN.

### finite_certificate 2026-11-25T14:52:44.295154+00:00
Replaced sampled rowpairs with exact1024row distinguishability via iterative partitioning; this checks all positive/negative pairs without quadratic enumeration. Exactfirstmove sweep443states:297collisioncuts,65restrictioncuts,80survive. No survivingfirstmove touchesx0 orx2; seed mayonly ORxi fori=1,3,4,5,6,7,8,9, keepingxi andconsumingseed. This concerns seed-live caseonly, notunusedseed.
Weak sampleddepth3runs didnotclose (171313states/72563frontier in180s; clippedseedfalsecap17 run300000states/152657frontier). Full-depthexact run nowadds semanticstate transpositions and4graphautomorphisms fixingseedpair. Allfigures are exploratory programresults, notLeanchecks.

## structural_proof caution 2026-11-25T14:55:20.141081+00:00

The endpoint OR-only equality discussion is conditional: seed may be unused, and existing4-gate lemmas L4093/L7085 require globalminimum on fullPetersen inputs. Minimality among seeded suffixes doesnotimply that. No result here asserts these reductions apply unconditionally.

## structural_proof CHECKED 2026-11-25T14:56:14.864102+00:00

`results/orch/lemmas/structural/SeedErase.lean` (125lines) passed `lake env lean` exit0; fullstdout/stderr in `/tmp/oec/pequalnp-pilot-134/seed-erase-check-003.log` (empty). It proves `circuit_erase_seed`: anyMonotone2 circuit computing Petersen from arbitrarymappedinputs plus x0 ANDx2 also computes it with that extra input fixedfalse. This is partialprogress only; it doesnotprove the18gate lowerbound or ruleoutNOT circuits. Removed duplicated pure-only scratchfile after fullproofpassed.

### Independent partial review 2026-11-25T14:56:55+00:00
- Status reviewer independently checked structural/SeedErase.lean: PASS as partial, not a full gap proof. Joint monotonicity plus minimal Petersen edge witnesses validates erasure of the nonedge seed0 AND2. Arbitrary input permutation function is handled pointwise. Imports and namespace satisfy format; no forbidden tokens, no executable/link, valid UTF8. 125 lines,5053 bytes. Agent reports Lean exit0 with empty diagnostics.
- L4093 core4 at661 is graph-free and needs no normalization or all-input counts; girth is discarded by final wrapper. Minimality is global, so applying to seed-prepended circuit needs a separate justification.

### Raw-raw lemma checked 2026-11-25T14:57:57+00:00
- RawRaw.lean compiled exit0; complete output in same folder RawRaw.validation.txt. Structural agent independently reviewed semantics and format PASS. Ready early partial push. No minimality assumption: every raw-raw AND/OR gate computing Petersen forces each distinct raw endpoint to have at least2 effective readers.
