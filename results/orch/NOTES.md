# L-meta-2583 orchestrator notes

Lease obtained 2026-11-25T08:45:19Z by root. Root alone renews/releases/submits.
Exact gap: /tmp/oec/pequalnp-pilot-76/gap.json; exact statement: /tmp/oec/pequalnp-pilot-76/statement.txt.
Use source /tmp/oec/pequalnp-pilot-76/lean-env.sh before Lean commands. Only 922 MiB disk remains, use narrow cached Mathlib imports. Current PEqualNP.Defs and checker prebuild passed.
Only allowed project module: PEqualNP.Defs. Final file lean/PEqualNP/Outside/L_meta_2583.lean. Helpers must live in own module namespace. No prohibited tokens, axioms, admissions, bv_decide, native_decide, strings or global options.
Each strategy owns a separate notes section below and separate files under results/orch/lemmas. Root integrates final proof. No agent may call desk, commit, push, or open a PR.

## Direct strategy

Before 2026-11-25 08:49:07 UTC, `direct_prime.lean` compiled with only `PEqualNP.Defs`: prime implicants are exactly incident point-line pairs, without plane assumptions. Root notified for checkpoint push.

The direct quantitative route needs size lower bound N*(q+2)-1. Canonical line-star circuit costs N*q inner ORs, N ANDs, N-1 top ORs and is read-1 on every incident pair.

At approximately 2026-11-25 08:50:50 UTC, `direct_canonical.lean` compiled with ONLY `PEqualNP.Defs`. It adapts accepted `L_meta_7684.lean` into our namespace and specializes to plane incidence: lemma `PEqualNP.Outside.L_meta_2583_aux.plane_read_one_upper` assumes only uniform line degree q+1 and produces an AO2 read1 circuit of size at most N*(q+2)-1 computing the exact incidence function. No geometry assumptions needed for this upper bound. `incidence_card_canonical` is an 8-line sum-rearrangement proof of edge count N*(q+1). File frozen for checkpoint push; root notified. Full log `direct-canonical-plane.log` has only inherited warnings.

Remaining obstruction for direct completion: prove arbitrary AO2 circuit size ≥ N*(q+2)-1, or weaker size comparison to some read1 circuit without the exact lower bound. The canonical upper bound is completely discharged.

At 2026-11-25 08:55:17 UTC, `direct_read_one_lower.lean` compiled: adapted accepted L_meta_4897 into own scoped namespace, only Defs, 1964 lines, giving the no-rectangle bipartite read1 edge-plus-cover bound. Structural agent supplied a compiled plane-cover wrapper; composing these in `direct_plane_lower.lean` to prove read1-plane size ≥ N*(q+2)-1 outright. This will formally identify the original replacement problem with the arbitrary-AO2 size lower bound once paired with the canonical upper construction.

## Counterexample strategy

At 08:53 UTC: READ1 is per-prime-implicant leaf multiplicity, not a globally read-once formula. Accepted L_meta_2237 gives the READ1 lower bound |E| + vertex-cover size - 1 for C4-free graphs. Fano has 21 edges and cover number 7, hence a 26-gate AO2 circuit would refute the replacement claim; an explicit star circuit uses 27.

Fano relation p = l or l+1 or l+3 in Fin 7. Exhaustive Python enumeration finds 21 positive edge pairs and 37 maximal independent sets; these 58 monotone boundary patterns characterize all 16,384 truth-table entries. SAT synthesis for 26 gates uses 5,928 variables and 164,821 clauses, with a capped 600-second CaDiCaL run. A separate stochastic circuit walk is running. No counterexample found yet. The encoding was validated against a known 27-gate circuit on every CNF clause and all 16,384 inputs.

Partial Lean file results/orch/lemmas/counterexample_fano.lean verifies plane axioms, circuit size/validity, and one-read proof trees for each incident pair; compilation fix in progress. SAT/search files and complete logs live under /tmp/oec/pequalnp-pilot-76/counterexample_* and fano26-*.

## Structural strategy

- `structural_geometry.lean` compiles: `incidence_card` proves the incidence edge count is `N * (q + 1)`; `point_degree` proves every point lies on `q + 1` lines by partitioning the other points into the lines through the fixed point with that point removed.
- Complete geometry build output is `/tmp/oec/pequalnp-pilot-76/structural-geometry.log` (exit 0, no diagnostics). The direct strategy has received the edge-count lemma.
- Canonical point-star cover has `N * (q + 1) + N - 1 = N * (q + 2) - 1` gates and is read-1. The unresolved step is relating arbitrary AO2 circuit size to this sharp cost.
- `structural_cover.lean` now also compiles (exit 0, empty `structural-cover.log`): every incidence vertex cover P,L satisfies `N ≤ P.card + L.card`, by regularity and two restricted-edge fiber counts. Both checkpoint files are frozen.
- Existing local `L_meta_6579.lean` is a general read-1 certificate for bipartite one-AND-level circuits. `L_meta_7684.lean` is the stronger canonical cover construction already adopted by the direct strategy.
- `structural_noc4.lean` compiles: two distinct points have exactly one common line, and two distinct lines have at most one common point. The 4897 theorem already handles its bipartite graph conversion internally, so a new graph construction is unnecessary.
- `structural_read_one_bound.lean` compiles: an explicit generic 4897 lower-bound parameter implies the sharp projective-plane read-1 bound `N * (q + 1) + N ≤ C.size + 1`. The direct strategy is replacing the parameter with its adapted accepted proof. This is a conditional wrapper, not the posted theorem.
- A census of local non-ReadK NoFourCycle statements did not locate an unrestricted sharp lower bound. Available routes retain hypotheses/deficits: 7241 needs all AND gates to reject nonedges; 3706 pays for ReadTwice edges; 3700 normalizes under exactly one junk AND and singleton rejection; 1491/5781 retain the Ustar deficit. Full census statements are in scratch `structural-noc4-statements.txt`.

## Reduction strategy

2026-11-25: Review confirmed L-meta-2583 is not open to reductions, so no reduction will be submitted. The natural conceptual split is exact lower bound N*(q+2)-1 plus canonical read-1 upper-bound construction, but the lower bound is the hard part.

Checked partial: `results/orch/lemmas/decomposition_minimal.lean`, 32 lines, proves that every nonempty Circuit predicate has a globally size-minimal witness, and among those a witness minimizing any Nat-valued structural measure. Lean exited 0; complete empty-success log is `decomposition-minimal-build.log` in scratch. Root notified immediately.

Existing normalization results worth integrating locally: L_meta_4293 (288 lines) proves Lift preserves AO2, output validity, size and function. L_meta_4295 (563 lines) reaches a Lift fixed point by the measure gates.length - belowCount. L_meta_1499 (1694 lines) reduces andPairs when a below-F AND is nested in another AND of a least circuit, preserving junk cardinal. Only Defs is allowed, so using their content requires local helper copies.

Best compiled checkpoint (08:54 UTC): `results/orch/lemmas/decomposition_graph_minimal.lean`, 725 lines, includes the earlier helper and a local adaptation of L4295. New endpoint `PEqualNP.Outside.L_meta_2583.Normalization.exists_least_graph_fixed`: any AO2 circuit for a graph function with a true input has a no-larger least AO2 replacement satisfying the actual library predicate `Core.IsLiftFixedPoint`. Full Lean log `decomposition-graph-minimal-build.log`; exit 0, no warnings. This is the completed first normal-form stage from the desk sketch. Earlier normalization/core scratch files are strict predecessor snapshots, so only newest content is needed in a final proof.

The lower_bound strategy owns the complementary strict deletion lemma: a least AO2 circuit cannot feed an AND with a wire already below F. These two facts still leave blocks containing junk AND gates; the exact block-cost/read-1 replacement theorem remains open.

## Review strategy

## Lower-bound strategy

2026-11-25 08:54:43 UTC: generic quadratic monotone circuit normalization is false in general (local note cites Jukna's single-level counterexamples); projective-plane C4-free structure must be used. A useful strict normalization step is now compiled in results/orch/lemmas/lower_bound_and_erasure.lean: when an AND gate reads a wire below the final output function, erase that AND and redirect its readers to the below-output operand. At negative inputs that operand is false, so evaluation is unchanged; at positive inputs erasure only increases wire values, so the output stays true. This lowers size by one while preserving AO2 and function. Therefore a least AO2 circuit has no AND operand below its output. The new AndErasure namespace starts after the shared Normalization prefix; integrate only the new namespace to avoid duplicate helpers. Full standalone compilation exited 0 with an empty diagnostic log lower-bound-and-erasure.log. Remaining obstruction is bounding dirty blocks that reread variables; normalization alone does not establish their star-cover cost.

## Review strategy continued

2026-11-25 08:47 UTC. Current public desk snapshot (updated 08:46:16 UTC) confirms L-meta-2583 is open, but its row has no reductions:true. The sketch asks for cuts, yet intake closed PR #10947 at 2026-11-25T00:09:59Z explicitly because this step is not open to reductions. PR #7163 received the same refusal. Do not send a reduction unless the public row changes.

Complete GitHub search (total_count 5, incomplete_results false) found PRs #5064, #6987, #7163, #9168, #10947, all closed; zero open PRs, matching desk. Repository old name brilliant-hq redirects to open-goat. Public desk snapshot saved in scratch review-gaps.json.

Definitions checked: TopForm.IsAO2 requires AND/OR only, ReadsBack, and exactly two inputs per gate (repetition allowed). No constant gates. ReadK.IsReadK is the genuine joint vector recursion: one common proof tree must read each prime-implicant variable at most once. It is not the weaker scalar eachReadsAtMost. Invalid wire defaults cannot help under ReadsBack; output range is not stipulated but equivalence to this nonzero incidence function forces a meaningful output.

Accepted related proof L_meta_2237 (line 1877) shows any read-1 AO2 circuit on a C4-free graph gives a vertex cover T with edges + |T| <= size+1. L_meta_4897 (line 1929) gives the same inequality directly for rectangle-free bipartite incidence. For a projective plane |E|=N(q+1), minimum cover=N, so the requested theorem implies the full star bound N(q+2)-1 for every AO2 circuit, a substantive open lower bound. The obvious line-star construction gives matching read-1 upper bound. No definitional shortcut found.

Useful stronger upper-bound code already accepted: L_meta_7684, 1123 lines, constructs read-1 AO2 circuits for ANY finite bipartite edge set and ANY vertex cover with size <= edges + cover - 1. Its final theorem is at line 1123. Root cannot import this outside module under the assigned allowlist, but may adapt its code into own namespace. This removes the upper-bound difficulty; the target is therefore the circuit lower bound. L_meta_7639 line 1964 proves the matching read-1 lower bound edges+N for rectangle-free square bipartite graphs carrying a perfect matching.

Latest guard: helper declarations must be inside namespace PEqualNP.Outside.L_meta_2583 (or its _aux), with exact matching end; final theorem fully qualified at top level and last. No _root_, double quotes, bv_decide/native_decide, global options, or attributes except simp; forbidden text includes comments. Run outside-guard imports separately from check-lean.mjs because the latter does not enforce source format.

2026-11-25 08:49:35 UTC, independent pre-push checkpoint review of results/orch/lemmas/direct_prime.lean: PASS AS PARTIAL only. 72 lines, 2891 bytes; allowed import, own auxiliary namespace, mathematically correct disjointness and prime-implicant characterization, no axioms/admissions/forbidden tokens. Actual exported checkProofFile reported only the two expected missing-final-theorem messages. Compiler log direct-prime.log is empty; root/direct strategy reported compile exit 0. It is not yet a submission-ready proof and must not be represented as accepted.

2026-11-25 08:50:51 UTC, independent checkpoint review: structural_geometry.lean and decomposition_minimal.lean PASS AS PARTIAL. Geometry correctly double-counts incidences and partitions the other points by lines through a fixed point; minimality correctly minimizes natural gate count then arbitrary natural measure. Guard has only expected missing-final-theorem findings, no forbidden tokens. direct_canonical.lean was extended to 1160 lines during review; its original 1125 lines match accepted L_meta_7684 after namespace renaming and removing import Mathlib. Found one integration format issue: helper theorem Canonical at lines1122-1125 is outside an ownnamespace block; move it inside PEqualNP.Outside.L_meta_2583_aux before final submission. Plane upper-bound appendix is mathematically correct. These are partial checkpoints, not a full proof or accepted checker result.

2026-11-25 08:52:21 UTC, independent composed checkpoint review: PASS AS PARTIAL for named file SHA256 670c93a13b13d5927ca3579ee0c631e859cbbfb7db13acf9d55849973719d315. Exact bodies of prime, corrected canonical, geometry, and normalization files are present; 104 parsed declarations, no duplicate fully qualified names, permitted imports only, diff whitespace check passes. Source guard reports only expected missing-final-theorem. Normalization matches accepted4295 core after namespace renaming; added reflexive-transitive closure preservation and least normalized circuit existence are sound. This normal form only excludes mixed-below OR operands and does not prove blocks are stars or read-1.

2026-11-25 08:55:14 UTC, independent checkpoint3 delta review: PASS AS PARTIAL for structural_cover (152 lines), structural_noc4 (28), decomposition_graph_minimal (725), counterexample_fano (43), and only the new AndErasure namespace from lower_bound_and_erasure (lines300-496). All actual source guard findings are expected missing-final-theorem only. Cover bound is valid regular-incidence double counting; NoC4 facts follow unique lines. Graph minimality extension correctly derives output validity from one true input. Fano proves incidence axioms, 27-gate AO2 validity, and read-1 on incident pairs; full function-equivalence is not yet a theorem in that file. AND erasure preserves function by monotonicity on true inputs and the below-output operand being false on false inputs, contradicting leastness. Integrate graph_minimal instead of prior normalization/core and only AndErasure suffix to avoid duplicate names.

ReadK census repeated over all accepted L_meta files containing IsReadK (20 files), including multiline main theorem statements: no general size-preserving read-1 normalization already covers2583. L_meta_7344 repairs missing prime pairs with added gates, insufficient here; L_meta_6579 provides read-1 from separated AND operands. Remaining relevant results are canonical upper bounds or lower bounds assuming read1/2/3. Census in scratch review-readk-files.txt.
