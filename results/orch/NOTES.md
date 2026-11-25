# L-meta-2592 orchestration notes

Lease acquired 2026-11-25T14:14:44Z; only root renews and submits.

Task: rule out <=19-gate fan-in-two circuits containing a NOT gate computing Petersen edge function. Allowed project module: PEqualNP.Defs. Reductions open but 3 live slots occupied.

Each agent should append short findings with UTC time and strategy name. Put Lean experiments under results/orch/lemmas with distinct names. Do not modify the main proof file or git state.

## 2026-11-25T14:15:56.262052+00:00 definitions_audit
No obvious malformed-circuit loophole. Size counts every gate; sequential fold makes forward references false, never cycles. AND/OR fan-in ≤2 permits empty constants, unary copies and duplicate inputs. NOT uses only first input; second ignored. Missing output false. A NOT witness may be outside output cone, so useful-NOT assumptions need proof. All these effects fit standard circuits with free false constant.

## Lemma routes (2026-11-25T14:17:29.393891+00:00)

- Direct root proof is not already recorded. Three existing reductions R_meta_2592_271, _318, _408 all retain a hard lower-bound child.
- R2592_271 binaryFloor solved in L_meta_4725 (3224 lines): 15 + notCount <= size. Few-NOT child is L-meta-4727, not solved. Its reductions: _1 vacuous noNOT/hasNOT split (noNOT side L8021 solved); _17 functional compiler solved by L6060 but functional lower bound open; _53 signed circuit compiler solved by L7227 but signed lower bound open.
- Stronger solved full-Petersen nonNOT floor: L_meta_6581 (4555 lines), 16 <= countP (fun g => !g.op.eval [false]) gates. This is AND/OR count under FanInTwo, so <=19 permits <=3 NOT gates.
- R2592_318 last-NOT factorization is solved by L_meta_8295 (66 lines), prefix arbitrary FanInTwo, suffix Monotone2, sizes sum+1. Remaining separator lower bound is hard.
- L_meta_8033/8035/8037/8039 prove 9vertex-deletion graph size >=16 by cases 0/1/2 NOT; L_meta_8367 combines. L5367 gives size >=15+readers for Petersen with free NOT x0.
- Existing explicit 20-gate construction: L_meta_1755 (29 lines), sent to circuit_search.
- Descendant lower bounds L5236 (3..4 NOT) and L5238 (>=5 NOT) reject <=18 after free x0 OR x2, with normalized back references. Low-NOT sibling remains split by R5234_1 into 9vertex bound plus 0/1/2 NOT specialized reader-count cases.

## 2026-11-25T14:18:39.306113+00:00 elimination
L_meta_8367 internal graphLower gives full FanInTwo lower bound 16 for Petersen minus vertex 9, via monoRoot 15 and signedRoot 14. It is a 524,213-byte file (75 below file limit), so any reuse plus lift needs pruning. Generic projected_bound (lines577ff) tracks constant frontier mass after restrictions; no direct 4-gate deletion theorem. Found existing generic syntactic reader/fanout elimination in L_meta_314, lines1562-1595: for NoFunnel and nonconstant restrictions, either pin false removes >=3 or pin true removes >=4; stronger Pays pairs (3,3),(4,2),(2,4). This alone misses target20: pinfalse graph lower16 +3=19; pintrue graph becomes OR of3 variables plus six-cycle, upper11. Need extra NOT-specific accounting.

### Route follow-up (2026-11-25T14:20:04.701924+00:00)

- R5234_1 low-NOT hypotheses h_not0/h_not1/h_not2 remain unresolved in current repository: no final L theorem contains Strict 11 together with notCount, and no other R theorem contains that profile. h_p9 is L8367. Thus this reduction cannot currently close full gap by assembly.
- For 9vertex Petersen deletion, L1001 has explicit 16gate all-AND/OR witness. No final L theorem found proving >=17 when a NOT occurs. Existing L2161 exact-one-NOT and L2163 exact-two-NOT only prove >=16. A size16 circuit with a NOT remains worth computational testing before assuming optimal NOT-freeness.

## Independent partial review (2026-11-25T14:21:01.214205+00:00; lemma_routes)

Reviewed root_petersen.lean (43 lines), audit_last_not.lean (154), elimination_fanout.lean (69) as branch-preservation partials, not as a proof PR. Static verdict PASS for intended partial scope: UTF-8 regular nonexecutables, all under 7 KiB; allowed initial imports, own helper namespace, no banned text, strings, attributes, options, sorry, native decision or axioms. They intentionally contain no top-level posted theorem and therefore are NOT submission-ready.

Mathematical review: root_petersen establishes essentiality of each of the ten Petersen variables through a neighboring singleton witness; all neighborhood entries are valid. audit_last_not correctly excludes an output NOT fed by a monotone prefix using all-false/all-true inputs. Its scope is a unique NOT at the designated final output, not arbitrary circuits containing a NOT. elimination_fanout is a sound slot-count argument: total pins <=2s-1, used internal gates >=s-1, so s<2n forces a primary input used at most once. Its unary and live hypotheses require normalization/dead-gate removal before application to a raw FanInTwo circuit. No invalid mathematical assumption is hidden.

Compilation has not yet been independently observed; cache setup pending and no corresponding build logs were present at review. Full Mathlib imports in root/audit appear broader than needed but are allowed; import minimization should be tested only after compilation works.

## 2026-11-25T14:21:37.080949+00:00 definitions_audit single-use consequence
For every pair of distinct primaries v,w, Petersen does not factor through AND(v,w), or OR(v,w), plus the other nine primaries. Verified all 90 ordered pairs by direct Python truth evaluation. AND witness: choose neighbor u of v other than w, compare {u} and {u,v}; gate value stays false. OR witness: choose neighbor u of v nonadjacent to w and different from w, compare {u,w} and {u,w,v}; gate value stays true. Lean witnesses/funnel refutations appended in audit_last_not.lean, awaiting Defs build.

## 2026-11-25T14:21:52.617608+00:00 lower_bound
No direct NOT-specific four-gate deletion argument found. General NOT-free or monotone-optimality claims are unjustified: multioutput savings can in principle encode a degree-two graph function via selectors. Full-Petersen nonNOT floor16 leaves one to three NOT gates. Generic reader elimination only saves3 on false restriction, leaving the tight9vertex size16 case; pintrue has a cheap OR3 plusC6 residual. A pruned <=19 circuit containingNOT has <=18 binary gates and <=19 primary-input uses, so some of10 essential variables is read once; exploiting its computed/shared partner remains the obstacle.
Suggested focused counterexample search: minimum vertex-cover implementation uses9 gates for six OR-neighborhood outputs,6 centerANDs and5 finalORs. Any eight-gate implementation of that OR family withNOT yields19 total. circuit_search verified five covers, each with three induced matching edges and eight orientations, and is testing all40 families. Also suggested testing9vertex size16 with exactlyoneNOT to assess the optimal-NOT-free equality route.

## Circuit search 2026-11-25T14:22:24.266261+00:00

- Read exact Circuit and FanInTwo semantics; no useful semantic loophole.
- Known20-gate seed L_meta_1755 used; complete truth-table check passes. Python CNF encoding tested by fixed20-gate witness: CaDiCaL SAT.
- Original19-gate oneNOT SAT, first OR(0,1), timed out180s; no conclusion.
- C++ CGP19 search with NOT ongoing300s, best9 truth-table errors so far.
- Signed18-gate (free negation) SAT and CGP underway, no witness yet.
- Targeted 8-gate six-output OR-neighborhood families for minimum covers: first orientations0..4 UNSAT on112test assignments; 5..7 running. This is computational evidence for a restricted factorization route, not a proof of original gap.
- Petersen minus vertex9,16gates and exactly1NOT: SAT search launched180s.
- Search source: results/orch/lemmas/search_sat.py, search_star.py, search_cgp.cpp; all logs /tmp/oec/pequalnp-pilot-117/search/.

- Star-family search complete: all8orientations UNSAT (CaDiCaL exit20). Exact backtracking found120 Petersen automorphisms, min-cover orbit size5 and the orientation0 family orbit size20. All8orientations were tested directly, so cover transitivity covers all40 formulations (there are at least2orientation orbits). This remains restricted computational evidence, not a Lean proof or proof of the gap.

## 2026-11-25T14:27:04.504891+00:00 elimination checked components
- elimination_fanout.lean and stronger elimination_raw_fanout.lean both compiled with Lean4.36.0 (lake env lean, exit0, empty output). Prove single-use primary from binary fanin, unarygate, live nonoutput gates and size<2*inputs. Raw version accepts arbitrary Nat wires.
- elimination_live_retain.lean and stronger elimination_live_retain_each.lean compiled exit0. Prove first Live-step retains either / each / both operands when target row separation contradicts losing them. Paste-ready snippets in /tmp/oec/pequalnp-pilot-117/elimination/retain-snippet.txt and retain-each-snippet.txt; lower_bound informed.
- Caveat for signed binary lower18: pinzero after first AND or ANDNOT can produce two constant frontier terms. After first OR it produces one constant and a duplicate nonconstant input; current mass counts constants only. Generic duplicate surcharge is unsound (repeated-input XOR formula). OR needs special target reasoning or extra search, not a free duplicate charge.

## 2026-11-25T14:27:25.198823+00:00 definitions_audit checked funnel consequences
`audit_last_not.lean` now compiled with exact full Defs, exit0 and empty output. Checked wrappers exclude a sole-reader AND/OR gate combining two distinct primaries, independent of other gates or malformed wire references. Checked `petersen_no_primary_last_not_once`: a sole-reader primary cannot feed the last NOT (the suffix is AND/OR); no restriction on operations in the independent prefix. Combined with a quantitative count of t single-use primaries for t NOTs, at least one single-use primary must feed a binary gate with an internal partner, after degenerate normalization.

## Normalized live representative (2026-11-25T14:27:42.595753+00:00; lemma_routes)

New checked partial results/orch/lemmas/routes_normalized_live.lean: 637 lines, 29255 bytes, exact file compiled with lake env lean, exit 0 and no warnings. Complete log /tmp/oec/pequalnp-pilot-117/routes-normalized-live-final-build.log is empty. Baseline uses L7389 normalization and selected L551 dead-gate deletion lemmas; new wrapper proves a size-minimal equivalent Petersen representative D with backward reads, unary NOTs, output last, and every earlier gate read later. Crucially D retains a NOT or has strictly fewer gates than the original C. This closes the normalization/liveness hypotheses needed by the incidence argument, without assuming arbitrary circuits are well formed.

The wrapper chooses a minimum equivalent circuit and prefers the original if it is already minimum; normalization then cannot reduce its size, and the generic deletion argument proves liveness. If pruning erases NOT from a <=19 circuit, D has <=18 gates; a version of the incidence argument with s+1<2n still obtains a primary read at most once without needing a monotone lower bound.

No direct checked full-Petersen monotone >=19 or >=20 theorem was found in the current repository. Existing 2590 reductions still retain lower-bound children.

## Root re-plan 2026-11-25T14:32:09.301271+00:00

The strongest active route is the signed live-wire lower bound. All four cofactors for each primary pair are distinct, and a checked row table now forces both first-gate operands to remain available. Restricting a retained input false yields a robust proposed binary floor17 from the checked nine-variable floor15; first AND/ANDNOT may yield18. First OR creates a duplicate, whose elimination cannot be charged by the existing constant-mass invariant. Do not claim uniform floor18 yet.

Normalized-live and sole-primary-reader partials are checked and pushed. Search strategy: normalized signed18 and paid one-NOT19; star-cover eight-gate auxiliary strategy excluded by finite computer search, with kernel verification in progress. Limit heavy Lean to about2CPU and search to1CPU when possible; container quota4CPU.

## Circuit search update 2026-11-25T14:33:35.261345+00:00

- CGP original19:641.4million candidates, no exact witness, best9truth errors. Signed18:315.6million candidates, no exact witness, best9errors.
- Exact SAT original19 firstOR01 oneNOT180s, signed18 CaDiCaL180s, signed18Kissat300s, delete9target16oneNOT180s:all timeout/unknown, notUNSAT.
- Local exact repair of original19best with≤3changedgate definitions:UNSAT;≤4repair timedout180s. Signed18≤4repair timedout180s.
- Added colexfanin order restriction (search heuristic, no completeness theorem), signedwirephase normalization falseatallzero (AND/OR/ANDNOT/NOTAND), and2NOTexactcount mode. Paused/terminated extrajobs toreserve2CPUsforLean.
- Onlynormalizedsigned18SAT currentlyrunning; ABCcompile effectively1CPU, onecompilerpaused in scratch abc-paused-pids.json and MUST resumeonce remainingbuildwaits.
