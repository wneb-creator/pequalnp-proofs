# Circuit search: L-meta-2732

Started 2026-11-25 around 05:28 UTC. Scratch directory:
`/tmp/oec/pequalnp-pilot-70/circuit-search/`.

## Verified setup

- Heawood target has 21 minimal true rows and 37 maximal false rows (21 of weight 4, 14 of weight 5, 2 of weight 7).
- The 58-row vectors match the existing reduction `R_meta_2732_3.lean` (independent check by sat_review).
- All 65 canonical first-two-gate wiring patterns match the 336-element Heawood automorphism group (independent check by sat_review).
- Built official CaDiCaL source from GitHub in scratch. Version `3.1.0`, commit `e4d9bd93af444c6575a908a24da2c4130cb2a1c7` of `arminbiere/cadical`. Configured with plain `./configure`, compiled by `make -j4`. Compiler: `g++ (Debian 14.2.0-19) 14.2.0`; generated flags: `-Wall -Wextra -O3 -DNDEBUG`, with include paths `-I../build -I../src`. No external Python solver package was installed.
- `synthesize.py` constructs a one-hot fan-in CNF for AND/OR DAGs. The `sat_review` agent checked the mux, operation, and one-hot clauses independently.
- Added sound boundary nontriviality, adjacent-independent lexicographic ordering, and liveness constraints. A `--minimal` variant additionally excludes domination by earlier wire boundary signatures. The minimal variant only covers actual size-26 minimal networks, not padded smaller ones; the general search remains active independently.

## Checked baseline outside Lean

The fixed 27-gate star network satisfies the CNF, and `decode.py` independently verified all 16,384 input assignments. The explicit network is in `star27.json`; it was sent to formalization for a Lean baseline.

Its first two gates are OR(0,1), OR(0,2), canonical score 227. Its packed gate codes are:

`[4160,4224,4352,4225,4417,4290,4355,4995,5188,5125,5317,5062,5254,5382,1351,1608,1673,1482,1739,1548,1421,5980,6366,6431,6496,6561,6626]`

## Active searches

- `heawood26.cnf`: general 26-gate network, 7,381 variables and 201,740 clauses. Complete solver log: `heawood26-solve.log`. Initial wall budget 1,800 seconds.
- `minimal26.cnf`: liveness and semantic non-domination variant, complete solver log `minimal26-solve.log`. Initial wall budget 1,800 seconds. Paused at 05:34:31 UTC at root's request to reserve CPU for Lean builds; pause time is not search evidence.
- `live-dirty26.cnf`: prepared but not yet launched. Adds liveness and the necessary existence of an AND gate accepting some maximal false row (a consequence of the existing pair-clean lower bound for size26).

No 26-gate witness or exhaustive nonexistence certificate has been found yet.

At 05:40 UTC the general search had about 2 million conflicts and 253 CPU seconds, still running without a verdict.

## Induced-subgraph round

At 05:43:44 UTC the general solver was paused for a bounded exploratory round. The generic graph encoding was independently reviewed; fixed baseline circuits passed SAT plus full truth-table checks for every case.

- Three retained left vertices, orbit `(0,1,2)`: sought 10 gates; UNKNOWN after 60 seconds.
- Three retained left vertices, orbit `(0,1,3)`: sought 10 gates; UNKNOWN after 60 seconds.
- Four retained left vertices, orbit `(0,1,2,3)`: sought 14 gates; UNKNOWN after 120 seconds.
- Four retained left vertices, orbit `(0,1,2,5)`: sought 14 gates; UNKNOWN after 120 seconds.

These are sufficient subproblems: a one-gate improvement over their standard star circuit extends to a 26-gate full circuit by appending omitted stars. UNKNOWN is not a nonexistence claim. Complete logs and pause timing are in `subgraph-round.log` and `subgraph-round.json`.

The general solver resumed at 05:49:47 UTC after a pause of 362.57 seconds.

Also prepared a phase-guided CaDiCaL API driver (`phased.cpp`) and a canonical 26-gate network missing exactly one target edge (`near26.json`). The API driver passed a fixed-star SAT smoke test; its longer run is recorded below.

The API driver compilation uses `g++ -std=c++11 -O2 -I cadical/src phased.cpp cadical/build/libcadical.a -o phased` (paths resolved under the scratch search directory).

## First full-run result and rotation

The original general run ended at 06:02:13 UTC with UNKNOWN: 1,800 real seconds, 1,104.63 CPU seconds, 6,214,151 conflicts, and 100.54 MB maximum resident memory. Its 362.57-second pause is included in the real time. No SAT model or UNSAT certificate was produced. Complete log: `heawood26-solve.log`; metadata: `general26-result.json`.

To reproduce the original general CNF with the current generator, use `--gates 26 --no-liveness`. Byte equality was checked; SHA256 is `aea6b6c49eef86d3f33291c451834688d0afe697c24e2ff19832cf9fbc44875e`.

After root renewed the lease at 06:02:08 UTC, the phase-guided live+dirty search started around 06:02:31 UTC with a 1,800-second wall budget. It still allows repeated tail operands and smaller circuits padded by output copies. Complete log: `guided26-solve.log`; hashes and command: `guided26-run.json`.

That guided run finished at about 06:32:31 UTC with UNKNOWN: 1,800.10 wall seconds, 1,707.67 CPU seconds, 7,892,230 conflicts, and 100.43 MB peak resident memory. Complete result metadata: `guided26-result.json`. Its CPU slot was then left free for formalization's ambient-graph accounting Lean check before the next search.

## Optional degree-two shadow restriction

The generator now supports `--shadow-missing 1`, `2`, or `3`, defaulting to zero (disabled). For its constant-free forward binary networks it tracks exact formal linear support and the target squarefree degree-two monomials under OR as addition and AND as multiplication. The final constraint requires at least the requested number of absent target monomials.

The team's mathematical argument for requiring at least three missing monomials at size26 is independently reviewed in `quantitative-shadow-three.md`. This is not a Lean-checked nonexistence proof. The `sat_review` agent independently passed the encoder implementation: 1,024 exhaustive assignments for the actual recurrence/mux AST and 754 cardinality assignments for sizes up to seven and bounds up to three. Full review log: `/tmp/oec/pequalnp-pilot-70/sat-review/shadow-property.log`.

Regression checks at about 06:06 UTC: a unit-fixed 27-gate star fails the missing-three restriction, as it should; appending an AND output-copy gate gives a unit-fixed 28-gate circuit which satisfies it and still passes all 16,384 Boolean inputs. These SAT/UNSAT regression verdicts concern fixed test networks only, not the posted size26 search.

Prepared `shadow3-26.cnf` has 11,073 variables and 306,744 clauses. It includes liveness, dirty-AND existence, canonical prefixes, and the missing-three restriction. Its correct phase file is `near26-shadow3.phases`. After the accounting check passed, the 45-minute run began at about 06:33:32 UTC, with scheduled end around 07:18:32. Run metadata and complete output are `shadow3-26-run.json` and `shadow3-26-solve.log`.

`run_recorded.py` records complete output, hashes, wall/CPU use, and verdicts automatically. On SAT it also runs the existing full truth-table decoder and saves a verified witness JSON. It passed a fixed-circuit regression using the 28-gate AND-copy example.

## Prepared later refinements

Third-gate symmetry: `sat-review/add_third_symmetry.py` appends 3,715 conditional bans from the independently verified stabilizers of the canonical first-two wiring patterns. It rejects fixed-prefix metadata because the normalization argument is global over input relabelings and topological orders. My independent verifier checked preservation of every base clause and recomputed every added ban; a fixed 28-gate regression remained SAT and passed all 16,384 inputs. The current active run does not include this refinement.

Initial-gate non-domination: the optional `--minimal-prefix 20` constrains only gate indices 0 through 19 using the already reviewed boundary domination clauses. Root Lean-checked the exact twenty-gate lower bound for this target, so a minimum circuit has at least twenty genuine gates; padding is added only later. The `sat_review` agent independently reviewed the flag and exact lower-bound edge list. A fixed 28-gate network with an output copy is SAT for prefix20, but UNSAT for prefix28, directly confirming that later padding is allowed. Invalid prefix lengths are rejected before output creation. Larger prefix values without a matching lower bound remain deliberate restrictions.

The combined instance is `third-shadow3-prefix20-26.cnf` with 38,333 variables and 365,449 clauses. Its phase file is `near26-third-shadow3-prefix20.phases`. After lower_bound's restricted run ended and root renewed the lease, this combined run started at about 06:58:27 UTC for 2,700 seconds, with scheduled end near 07:43:27. Its metadata and full log use the same `third-shadow3-prefix20-26-` prefix. The earlier shadow3 run and its input file remain unchanged.

## Alternative backend and final-operation split

Prepared official Kissat 4.0.4 from `https://github.com/arminbiere/kissat`, commit `8af8e56f174b778aef3aa45af9f739b2a5f492c2`, in the job scratch directory only. Built with `./configure` followed by `make -j1`; compiler is GCC 14.2.0 (Debian 14.2.0-19), flags `-W -Wall -O3 -DNDEBUG`, linker `gcc`. Exact provenance and binary hash are in `kissat-metadata.json`; complete clone/configure/build output and capability help are preserved. The complete checkout and build occupy 7.2 MB. No upstream writes occurred.

`fix_final_op.py` preserves the source CNF and appends one unit selecting the last gate operation, updating the header and mapping. `third-shadow3-prefix20-and26.cnf` forces AND using literal `-36888`, with 38,333 variables and 365,450 clauses. The complementary OR unit partitions the models of the source encoding. Smaller witnesses may be padded with either operation, so this is an explicitly scoped root-operation portfolio rather than a new lower bound.

`run_kissat.py` records complete output, command, hashes, wall/CPU time, and verdict; any SAT model is independently decoded and checked on all Boolean inputs. At 07:09 UTC, the known fixed 28-gate AND-copy circuit was SAT with the AND unit and verified on all 16,384 inputs; forcing its fixed last gate to OR was UNSAT. Smoke artifacts use `kissat-smoke-fixedand28-` and `kissat-smoke-or28-` prefixes. These are encoding regressions, not answers to the 26-gate problem.

Recommended to root: when the first active slot opens, run Kissat's default balanced configuration with seed 1, no phase hints, final gate AND, and a 45-minute cap. This varies backend scheduling, preferred assignments, and the output operation compared with the existing CaDiCaL near-star runs. At this checkpoint no such long run has started; both previous runs remain unchanged and active. Independent review of the new split/runner was requested from sat_review.

At 07:18:32.638172 UTC the first shadow-three run finished UNKNOWN: 2,700.233 wall seconds, 2,158.767 CPU seconds, 8,801,911 conflicts, maximum RSS 109.41 MB. Root requested a short CPU window for Lean checks; both active SAT children were paused from 07:16:45.574106 to 07:17:45.577744 UTC, lasting 60.004577 seconds. Their recording drivers and original wall deadlines were unchanged. The event is preserved in `verifier-pause.json` and both run metadata files; the completed shadow-three result also includes the pause and unpaused wall time. UNKNOWN is not a nonexistence result.

repo_review independently passed the Kissat split/runner, exact base-clause preservation, unit polarity, provenance, and smoke results. Root accepted the proposed 45-minute AND-root run; it is waiting for the required fresh lease renewal before launch. The combined CaDiCaL run continues to its original 07:43:27 deadline.

After root renewed at 07:18:51 UTC (expiry 07:38:51), the approved Kissat AND-root run started at 07:19:05.026189 UTC with a 2,700-second wall cap, scheduled to finish around 08:04:05. Exact command: `kissat/build/kissat -s --time=2700 --seed=1 third-shadow3-prefix20-and26.cnf`. It uses the default configuration, no phase hints, and no proof trace. Metadata and complete output are `kissat-and26-run.json` and `kissat-and26-solve.log`; any SAT model will be independently checked on all 16,384 inputs before it is reported as a witness. This run explores the final-AND branch of the restricted shadow-three encoding; an UNSAT verdict would retain that scope.

## Prepared cofactor construction

Constructive independently analyzed lower_bound's actual 30-row candidate: it is a 26-gate single-level network computing precisely the Heawood graph plus `(0,13),(3,13),(5,13),(6,13)`. It has 49 false-positive assignments and no false negatives among all 16,384 inputs. The previously unsolved 31-row query is not a candidate.

Let `F0` be the edge function after deleting vertex 13 and let `A = x1 OR x2 OR x4`. The full target is `(F0 OR A) AND (F0 OR x13)`. A sufficient focused strategy is therefore a 23-gate `F0` circuit that also makes `A` available internally; appending two OR gates and one AND gate yields 26 gates. This is a restriction for finding a witness, not a complete encoding of all possible target circuits.

Prepared `f0-available-a23.cnf` has 13 inputs, 18 edges, 48 boundary rows, 5,452 variables, and 122,718 clauses. Generation used `synthesize.py --gates 23 --edge-file f0-available-a-graph.json --no-canon --no-liveness --no-lex-order`, then `f0_available_a.py fix-prefix` appended six units fixing gates `OR(1,2)` and `OR(4,13)`. The second output is `A` at wire 14. Canonicality and adjacent lex ordering are disabled because this forced auxiliary prefix need not be a global normal form; liveness is disabled because the auxiliary output may be unused by `F0` itself.

The helper's `extend` mode shifts every generated wire by one to insert the omitted input 13, then appends the three assembly gates and exhaustively verifies both functions. A known 25-gate baseline (the auxiliary prefix plus the standard 23-gate `F0` star network) produced a SAT fixed-network smoke test and passed all 8,192 inputs; its 28-gate extension passed all 16,384 inputs. Complete smoke output is preserved. No long search on the focused 23-gate instance has started. Independent review was requested from repo_review.

repo_review independently passed the focused encoding and extension: exact base regeneration under the stated flags, the six appended units, the auxiliary wire offset, the graph identity, and all 16,384 inputs of the smoke extension.

## Workspace restart and focused search

Root reported a workspace restart at approximately 07:28 UTC. At 07:31:56 UTC, the previous combined CaDiCaL process and Kissat AND-root process were observed as zombies with RSS 0. Neither produced a solver verdict. Their final metadata now records `INTERRUPTED`, with null exit code, termination timestamp, and verdict; no elapsed time to observation is presented as solver runtime. Complete surviving logs remain intact at 186 and 92,889 bytes, respectively. `restart-process-observation.txt` preserves the process observation, and each result JSON records the corresponding log hash. These interruptions are not UNKNOWN solver returns and provide no nonexistence evidence.

After root renewed at 07:28:56 UTC (expiry 07:48:56), root authorized the reviewed focused search. `f0-available-a23` started at 07:32:21.948951 UTC using Kissat's default configuration, seed 1, and a 2,700-second wall cap, scheduled through approximately 08:17:22. Its run metadata and complete output use the `f0-available-a23-` prefix. Only this one solver was restarted; the other CPU slot was left available for environment recovery. On SAT, the runner checks all 8,192 inputs of `F0`, after which the reviewed assembly helper will check the resulting 26-gate full circuit on all 16,384 inputs.

Root corrected the construction budget: when `A` is already available, append `AND(x13,A)` and `OR(F0,new)`, using only two gates. Thus 24 gates for `F0` suffice. The previous 23-gate search was valid but unnecessarily strong; root explicitly stopped it at 07:36:02.562107 UTC after 220.588 wall and 218.811 CPU seconds (observed exit -15). It is recorded as deliberately INTERRUPTED, not a solver verdict. The helper now defaults to this direct two-gate extension; `--method shannon` preserves the earlier three-gate construction for reproducing its historical smokes.

After repo_review independently checked the correction and the complete 25-to-27-gate smoke, the corrected `f0-available-a24` run began at 07:38:57.223636 UTC, following root's 07:37:35 renewal. Its 2,700-second cap ends around 08:23:57. The helper hash is preserved in the run metadata. No first-pair shape is assumed: the posted theorem existentially chooses its two initial gates and requires only automorphism-minimal pair score, so the checked generic prefix normalization applies to an A-first witness.

## Exact local repair neighborhoods

`repair_base.py` is a separate copy of the reviewed generator with optional repeated operands in the first two gates. The repair bases disable canonical prefixes, adjacent lex ordering, liveness, domination, shadow restrictions, and nontrivial-signature restrictions. Only sorted commutative fanins, forward wiring, AND/OR semantics, and exact target boundary outputs remain. The original generator and all active input files are unchanged.

`repair_neighborhood.py` measures operand replacements modulo commutativity, plus AND/OR operation flips. A per-gate orientation variable chooses the better matching to the seed's unordered operand multiset; a signed-literal sequential counter enforces the total budget. Root independently reviewed this encoding, with hashes in `repair-review.json`. Exhaustive tests cover 5,056 cardinality assignments and 72 operand-matching cases. Fixed-seed smokes distinguish an incorrect 26-gate seed at distance zero (UNSAT) from the exact 27-gate baseline at distance zero and a one-operation repair (both SAT, all 16,384 inputs checked).

Completed restricted searches: near26 at budget 2 was UNSAT in 1.356 wall seconds; CEGIS30 at budget 2 in 0.502 seconds; near26 at budget 3 in 4.183 seconds; CEGIS30 at budget 3 in 1.372 seconds. These exclude only the named fixed-slot neighborhoods, not general 26-gate circuits. All commands, hashes, complete logs, and results are preserved. A separate simplifier removes idempotent, duplicate, and dead gates, then pads at the output; it passed full-input checks and supplies distinct first-two fanins for any repaired witness before Lean prefix normalization.

## Correlated residual cone

Constructive supplied a new architecture: fix the three left stars at vertices 1, 2, and 4 (11 gates including their union). Their three opposite-edge OR sums are free inputs to a residual K4-incidence cone. The residual has ten actual variables, three correlated OR signals, twelve positive edge rows, and twelve maximal false rows. A 14-gate cone plus the fixed 11 gates and final OR gives 26 gates.

`correlated_synthesize.py` validates the underlying extrema and cut evaluations, then constrains only the 24 reachable boundary rows. It does not treat all 2^13 signal combinations as required inputs, and liveness on the redundant cut signals is forbidden. The candidate has 2,085 variables and 37,549 clauses. `decode_correlated.py` checks every one of the 1,024 actual residual inputs, assembles the full circuit, and checks all 16,384 original inputs. A fixed 15-gate baseline is SAT with and without lex-normalized ordering; a normalized fixed 14-gate near-miss is UNSAT. sat_review independently checked the encoder, decoder, complete model clauses, embedding, and both smokes.

The reviewed `matching-cut14` run began at 07:53:03.367750 UTC after root's 07:51:21 renewal, for 2,700 seconds, scheduled through approximately 08:38:03. Its source hashes and exact candidate hash are in the run metadata. It runs alongside F0+A24. Any UNSAT result would be scoped to this fixed-three-star architecture; a SAT result is automatically expanded to a checked 26-gate candidate for the existing Lean assembly pipeline.

Separate, independently reviewed family encoder/decoder copies now support arbitrary OR supports and prefix lengths. They verify all actual underlying assignments, every cut-wire identity on all 16,384 original assignments, and the complete embedded output. The active matching-cut sources remain unchanged. The noncollinear three-star family has seven variants, 11 actual variables plus six cuts, and 27 boundary rows; its variant-zero 15-gate baseline passed all 2,048 underlying and 16,384 full inputs. No long search in that family has started.

The five-star fixed prefix leaves a six-gate residual target with seven actual variables, four free cross-OR cuts, and ten boundary rows. The reviewed candidate had 497 variables and 5,489 clauses. A fixed seven-gate baseline passed all 128 underlying and 16,384 full inputs; the fixed six-gate near-miss was UNSAT. Root authorized a short third solver. The unrestricted-within-this-architecture six-gate probe started at 08:09:41.020707 UTC and returned UNSAT at 08:09:42.318564, using 1.292 wall and 0.864 CPU seconds. This is a solver result for the fixed five-star architecture, not a Lean refutation of the posted gap.

The four-star family has six independently reviewed variants, ten actual variables plus eight cuts, and 17 boundary rows. Its candidate has 1,399 variables and 24,691 clauses; the eleven-gate baseline passes all 1,024 underlying and 16,384 full inputs. Root authorized two sequential 120-second third-solver probes. Variant zero ran from 08:11:49.066058 to 08:13:49.119517 and returned UNKNOWN (120.048 wall, 73.561 CPU seconds). Variant three ran from 08:14:41.846077 to 08:16:41.869187 and returned UNKNOWN (120.019 wall, 80.862 CPU seconds). Both full logs and result metadata are final; no probe was extended. Constructive is separately preparing a joint selector encoding for all six choices.

## Prepared later options

The F0+A24 tail-only lex variant is separate from the active run. `f0_tail_synthesize.py --lex-start 3` compares adjacent gates only within the unfixed tail, skipping the fixed-prefix boundary. Its topologically sorted 25-gate baseline was SAT, passed all 8,192 inputs, and its direct 27-gate full extension passed all 16,384 inputs. It is prepared for later use, with no search launched.

`add_raw_fanout.py` adds the reviewed necessary condition that a gate on two distinct raw inputs must have another direct consumer of each raw input. A unique AND use would restrict that vertex to degree at most one; a unique OR use would force a forbidden neighborhood inclusion or singleton acceptance. Root and lower_bound independently reviewed this argument; lower_bound also reconstructed every clause and checked the known 27-gate full model on all 16,384 inputs. This argument has not been described as Lean-checked.

The prepared later OR-root candidate is `general-or26-fanout.cnf`: third-gate symmetry, shadow-three, prefix-20 nondomination, final OR, and 4,732 new fanout clauses. It has 38,333 variables and 370,182 clauses, SHA256 `f870da9b0683e0055ee77c830296a760e84b38f9185d2803288ad0a01df26024`. lower_bound independently confirmed all 365,450 base clauses were preserved, IDs unchanged, and the new clauses exact. No run has started yet; any verdict retains the explicitly encoded restrictions and the previously noted status of the shadow argument.
