# L-meta-670 orchestration

Lease acquired 2026-11-25 03:00:15 UTC. Only root handles desk, git commits and pushes.

Goal: exact posted 9-input Petersen-minus-vertex 15-gate lower bound, imports PEqualNP.Defs plus Mathlib only. Three reductions already live. Append dated findings here, and keep candidate Lean under results/orch/lemmas or job scratch.

2026-11-25T03:01:49.272223+00:00

## Inventory (status_review)
- Current upstream has first-gate cases NOT0 L1665, NOT4 L1666; AND reps L1667–1672 (01,02,03,04,06,46); OR reps L1673/1674/1676/1677/1678 (01,02,04,06,46). Original OR03 L1675 absent.
- L4734 packages all six AND reps using only PEqualNP.Defs, 381605 bytes. L1680 proves removal of a constant/copy gate, 28807 bytes. Individual case files are 200–518KB, so naive inlining will exceed final 512KiB limit; shared certificate machinery likely needs deduplication.
- GitHub canonical repo is open-goat/pequalnp-proofs. Complete search census for L-meta-670: 11 matches, actual L670 proof PRs all closed; R670719 PR11232 is open although desk says three reductions live.
- Public sketch path https://pequalnp.com/routes/lgp/own/filing/petersen/SKETCH.md inaccessible via web tool; not assuming contents beyond desk sketch.
- Detailed theorem inventory saved in /tmp/oec/pequalnp-pilot-61/petersen-theorem-inventory.txt; candidate list likewise petersen-candidate-files.txt. Search for newer OR03 and normalization ongoing.

## 2026-11-25T03:03:57.199407+00:00 — normalization agent

- Re-derived graph automorphism group by enumerating degree-preserving permutations: exactly 12.
- Kernel-checked 53-line `results/orch/lemmas/Normalization.lean`: explicit table, bijectivity, exact edge function invariance, vertex reps 0/4 and six pair reps. Build exit 0, empty diagnostics in job scratch normalization-build.log. Root notified immediately for early push.
- Status reviewer found full stronger normalization already checked in `L_meta_4334.lean` (36,153 bytes, 714 lines). Its `priority_seed` helper exactly yields the first-gate cases needed by R670419, using only Mathlib+Defs. Preparing inlined component for integration; no need reprove generic cleaning.

## 2026-11-25T03:04:09.846276+00:00 — toolchain/search

Official Z3 5.3.3 installed in job scratch. Python exhaustive truth table confirms the explicit 16-gate monotone construction. `results/orch/lemmas/Search.lean` proves this upper bound with `decide +kernel`; `lake env lean` exited 0. This does not prove the posted 15-gate lower bound. Full log: `/tmp/oec/pequalnp-pilot-61/search-upper-lean.log`. A normalized 15-gate SMT search with first AND(0,1) is running; any SMT UNSAT remains computational evidence until independently certified in Lean.

2026-11-25T03:04:25.724314+00:00 status_review pivotal inventory update:
- Full priority normalization already checked in L_meta_4334.lean (36153B), exactly R670419 first hypothesis. L4336 is six AND suffix cases; L4338 is both NOT suffix cases (~513KB), leaving priority OR family L4340 unmerged.
- IMPORTANT: missing OR03 full lower bound already lives as helper L_meta_5120.bound, lines6138–6163, with NO reader-count premise. Its theorem: FanInTwo C -> first wire9 = x0||x3 -> circuitFun9 C = edge -> 16≤C.size. The final L5120 statement's reader-count hypothesis is unused. Thus every original first-gate case has a checked implementation somewhere.
- L2681.petersen_binary_lower lines3127–3146 proves arbitrary target circuit has 13 non-NOT gates. Binary-cost cases with >=3 NOT are therefore done mathematically.
- Shared machinery/certificate deduplication and total512KiB limit now main assembly issue. Finite_verification is extracting OR03 and assessing dedup; normalization agent informed about L4334; structural informed reader≤2 need not be proved for L5120 route.

## Restriction mathematics 2026-11-25T03:04:33.376413+00:00
- The six degree-three vertices form cycle 0-1-2-3-8-5-0. Vertices 4,6,7 subdivide its three opposite chords, so the graph is K3,3 with a perfect matching subdivided.
- Exhaustive finite independent-set calculation: deleting degree-two vertex gives 8 vertices,10 edges,alpha4 and star-cover upper cost13; deleting degree-three vertex gives 8 vertices,9 edges,alpha4 and upper cost12. These are upper formulas, not asserted general circuit lower bounds. True cofactors have corresponding upper costs10 and8.
- OR03 firstgate factors the star at4. Remaining graph G-4 has OR03 endpoints with disjoint neighbor sets {1,5} and {2,8}. Could reduce hard case to conditional cofactor bound if required.
- Generic direct-reader saving is already proved: Helpers/Readers.lean save accepts any clean circuit and finite set of gates reading constant-status wires; rc_input marks every direct input reader for either restriction value. Hence three distinct readers save three gates (clean NOT arity handled by simplification). Cofactor13 lower bound would imply at most2 direct readers for size15.
- Parent found unconditional L_meta_5120.bound for OR03; reader-count route paused in favor of fourteen-case assembly.

## 2026-11-25T03:04:58.522257+00:00 — full normalization component ready

`results/orch/lemmas/NormalizationFull.lean` (36,068 bytes, 713 lines) compiled with exit 0. Full empty diagnostics: `normalization-full-build.log` in job scratch. This adapts checked `L_meta_4334.lean` by renaming its namespace to `PEqualNP.Outside.L_meta_670.Normalize` and moving its final theorem inside as helper `normalization`. Only imports Mathlib and PEqualNP.Defs. `normalization` gives exactly the R670419 normal premise: a suffix circuit D with D.size+1 ≤ C.size, canonical NOT0/4 or six binary pair representatives, AND/NOT/OR priority restrictions, exact suffix evaluation with appended seed. Root notified immediately; component can be concatenated after removing duplicate import lines.

## 2026-11-25T03:06:24.491419+00:00 — computational search stopped

Full 512-row synthesis for 15 gates with first AND(0,1) returned UNKNOWN after 180.47 seconds (timeout). Two boundary-row CEGIS searches, one monotone with first AND(0,1), one at most two NOT gates with first NOT(0), were interrupted unresolved when all fourteen proved cases were located. No 15-gate witness or UNSAT certificate obtained. Search scripts and full logs remain under job scratch. Switching to self-contained raw proof aggregation.

## 2026-11-25T03:07:40.485490+00:00 — suffix-to-circuit bridge compiled

`results/orch/lemmas/Prepend.lean` compiled exit 0 (empty `prepend-build.log`). Namespace `PEqualNP.Outside.L_meta_670.Seed`. `seedCircuit D k a b` prepends the legal fanin-two seed gate. `seed_fanin`, `seed_size`, `seed_eval`, and `seed_first` prove legality, exact size increase by one, suffix evaluation equivalence, and semantic first-wire value. This lets Normalize.normalization feed every existing whole-circuit first-gate lower-bound case. APIs sent to assembly authors and root immediately.
