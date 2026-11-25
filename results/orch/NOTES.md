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
