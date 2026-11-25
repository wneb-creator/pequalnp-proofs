# Combinatorial strategy for L-meta-2592

2026-11-25T14:06 UTC: repository and definition audit complete. Exact circuit semantics allow invalid reads only as false, empty gates as constants, and NOT ignores additional inputs. FanInTwo really excludes MOD and MAJORITY; no semantic shortcut found.

## Existing useful checked components

- `Outside/L_meta_6194.lean` (144705 chars / 3255 lines) proves at least 15 non-NOT gates for the full Petersen function. Its generic branch-count proof requires at least six first branching roots and ten essential inputs, yielding 10 - 1 + 6 = 15 binary gates.
- `Outside/L_meta_4725.lean` supplies the same result directly as `15 + notCount C ≤ C.size`; semantic agent is building the >=5 NOT excluded partial.
- `Outside/L_meta_3400.lean` and `L_meta_5094.lean` prove 13 binary gates for the nine-vertex deletion graph.
- `Outside/L_meta_10792.lean` does not contain a general single-NOT elimination theorem. It establishes binary lower bound 10 for one seven-vertex graph and gives an explicit monotone size-11 witness; any NOT already costs at least 11, allowing wholesale replacement.
- The 18-gate full Petersen lower bound occurred only as a hypothesis in reduction `R_meta_4031_1`, not as a completed proof in the surveyed files.

## Restriction bottleneck

Petersen minus one vertex is a nine-vertex, twelve-edge graph with expected/target lower bound 16. Setting that vertex true leaves three free OR variables and the edge function of a six-cycle, whose standard upper bound is 11 total gates. Generic three-false/four-true gate elimination therefore gives no contradiction at 19. A successful restriction proof must exploit an actual NOT gate to force a false restriction saving at least four gates, or use a stronger paired restriction.

For two false inputs, adjacent deletion leaves eight vertices and ten edges; nonadjacent deletion leaves eight vertices and nine edges. Their cover-circuit upper bounds are 13 and 12 respectively. One would need savings of seven or eight gates, respectively, to contradict a 19-gate circuit (assuming these upper bounds are also established lower bounds).

## Research checked 2026-11-25

The search engine read the site's primary paper page `https://pequalnp.com/papers/note-1` (opening directly failed in the web tool). It identifies exact lower bounds for forests, cycles, and long-thread graph classes, not arbitrary girth-five cubic graphs. It explicitly distinguishes monotone formula lower bounds from general monotone circuit bounds; those cannot justify Petersen size 20. No general single-NOT elimination theorem was found in allowed-host searches. These searches do not establish nonexistence of such a theorem.

## Current direction

Investigate 1..4 NOT gates, especially whether the equality case of the binary floor (15 binary gates plus four NOT gates) forces extra branching or a removable gate. Requested the counterexample agent to isolate the 4-NOT SAT subcase.

## Checked partial: pair separation

2026-11-25T14:12:32.642512+00:00: `results/orch/lemmas/Combinatorial.lean` compiles with only `PEqualNP.Defs`. Every pair of distinct inputs has private-neighbor assignments making the function equal either selected input. Consequently no single Boolean summary of that pair can determine the function under all external assignments. `cofactorKeepsOtherInput` gives exactly the negation of the conclusion of L5971 `single_fanout_first_gate`, so every first-gate input must have another binary reader in a minimal signed circuit.

Potential stronger route: if a first signed-AND gate has a positive input, setting that input false deletes it, another reader of the input, and a consumer of the first gate. The latter two must be distinct by signed-AND absorption/minimality. This could save three binary gates and lift the nine-variable floor15 to18, leaving only a first OR-of-positive-inputs case. This last structural claim is not yet proved.

2026-11-25T14:14 UTC: added and compiled all ten vertex automorphisms in `Combinatorial.lean`. `vertexPerm v` sends vertex0 to v, is bijective, and preserves `pet`. This transports a deletion-at-zero lower bound to any chosen first-gate input. Full helper file now105lines; build exited0 with empty stdout/stderr.

L5971 has stronger generic weighted deletion results already: `elim_ge_4_same` gives four binary deletions when a first-gate variable and another gate use the same signed polarity and it is set to the blocking value; `elim_ge_3_opp` gives three at either chosen value for opposite polarities, assuming the restricted function is nonconstant. Together with the compiled cofactor lemma, these may give19binary for positive/same first-gate cases and18binary for opposite cases. They do not alone settle the first OR case or every one-NOT circuit.

2026-11-25T14:20 UTC: a census by exact nine-input theorem shape (rather than comments containing Petersen) found a complete bound previously missed: `L_meta_4033.lean` proves the nine-vertex deletion function has no circuit of size15. Its final `directSplit monoRoot signedRoot` combines a monotone15 impossibility certificate with free-complement binary14 impossibility. This does not imply that a NOT-containing circuit must exceed16. `L_meta_8035` and `L_meta_8957` carry the monotone part alone; their files are approximately485KB and the full L4033 is approximately516KB, so naïve concatenation with the current partial cannot fit the512KiB submission limit. Shared certificate infrastructure can be deduplicated, but the additional monotone tables and smaller-graph proofs remain substantial.

The full10-input census found no stronger completed free-OR suffix lower bound than L5236. Several superficially relevant later files (L8021, L9031, L9037, L9039, L7314) settle trivial or conditional normalization cases, not the missing19-gate lower bound.

## 2026-11-25 14:25 UTC — restriction-certificate search

The inverse automorphism helpers in `lemmas/Combinatorial.lean` compile with exit 0 and empty stdout/stderr. Reviewer independently checked all inverse tables. The file is 129 lines / 4768 bytes; `vertexInv_zero` sends an arbitrary restricted vertex to vertex 0, and `pet_vertexInv` preserves the Petersen function. Semantic agent owns the cofactor-floor bridge.

Extracted 295 certified induced-subgraph lower bounds from `L_meta_5236.lean` via its `known*` data and all 120 Petersen automorphisms. Scratch `certificates/zero-cuts.json` records each removed set, lower bound, representative 9-vertex mask, witness permutation, and source certificate. Independently checked every witness is a permutation preserving the 15 edges, sends some removed vertex to 9, and produces the recorded retained mask. Bound distribution: one deletion gives 15; two deletions gives 12 for nonedges (30) or 13 for edges (15); three deletions give 8 (20), 9 (60), or 11 (30); four deletions give 7 (60) or 8 (70). These are computationally extracted existing certified bounds, not a new theorem.

Applying those cuts to toolchain agent's exact Live-state prefix search for 17 signed binary gates reduces the edge-first-OR branch from 19,703 states at depth 4 to 1,895; depth 2 has 9 states and depth 3 has 142. Nonedge-first-OR has 24 states at depth 2 and 480 at depth 3. Root-pair polarity restrictions from checked `FirstGateCasesSuffix` yield the same surviving edge states through depth 3, so these cuts already detect the local polarity obstruction.

The next pilot, `certificates/prefix_provenance.py`, records each prefix gate's two input truth tables. For each restriction it tracks sets of gate indices sufficient to construct each restricted value and charges only the dependency closure needed for the live state. This removes projected dead gates from the upper bound on supply cost. Edge depth 3 is now 139 states. Search remains incomplete; no signed lower bound of 18 is established.

## Mixed restrictions and representative prefixes

The complete provenance pilot reached edge depth 4 with 1,793 states and stopped at its 302-second cap during depth 5 (715/1,793 parents processed, 7,836 children). No lower-bound conclusion follows. Testing 1,300 restrictions with one input fixed true and up to three inputs fixed false rejects 534 of these depth-4 states. Exactly the same 534 are rejected by just ten restrictions: fix a vertex true and all three neighbors false. The residual is the six-cycle and already has signed lower bound 8 in the L5236 certificate family. Thus the ten cuts require no new additive lower-bound theorem. Saved their JSON and an updated search script in results/orch. A separate Lean helper is being compiled to equate the mixed closed-neighborhood restriction with the all-false closed-neighborhood restriction.

A prospective concern about reader-budget pruning under state-only deduplication was resolved: the reader-bound proof uses only well-formedness and computes, not minimality. Concatenating any fixed valid prefix with a hypothetical state continuation gives a computing circuit, so its three primary readers would contradict the general bound even when another history reaches the same state. Few-nots agent checked the generalized reader bound. Moreover, universal binary lower bound 17 makes every computing circuit of length at most 17 automatically minimum, supporting phase constraints on representative-prefix completions as well.

## Pause at 2026-11-25 14:43 UTC

Root reported a desk lease error and instructed all proof/search work to pause. Stopped the active depth-6 search immediately with interrupt (exit 130); complete stdout/stderr are preserved. The last complete edge-first-OR checkpoint is depth 5, with 3,202 surviving states after all 1,259 depth-4 parents. Saved it compressed as `combinatorial_edge_depth5.json.gz`. The interrupted depth-6 log records 1,850 of 3,202 parents and 771 children; its in-memory child table was not written before interruption, so only the complete depth-5 checkpoint should be used to resume. `combinatorial_prefix_depth6.py` was made relocatable to these result files after the pause; that path-only edit has not been executed.

`lemmas/MixedC6.lean` compiled successfully, with empty stdout/stderr, and received an independent audit PASS. It is 146 lines / 5508 bytes, SHA256 c88b64521bf9655a5f6ed73ccedc6890570a06311622d05dc9371630f5f79a1d. It adds only the finite mixed-restriction identity to the previously checked 129-line Combinatorial component. No complete proof of the posted gap or signed lower bound 18 was obtained.
