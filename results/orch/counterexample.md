# Counterexample strategy for L-meta-1896

No witness found yet. The circuit definitions have no immediate constant or forward-reference loophole: nullary AND is true, nullary OR is false, unary gates copy, and unavailable wires read false.

Independent finite enumeration gives 468 required maximal negatives, with 234 of each side-size `(3,4)` and `(4,3)`. The 236 excluded maximal false supports have types `(2,6)/(6,2)` (78 each), `(3,3)` (52), `(1,9)/(9,1)` (13 each), and `(0,13)/(13,0)` (one each). Minimal accepted supports through degree four are the 52 incidence pairs plus 52 collinear point triples and 52 concurrent line triples. The geometry agent strengthened this to an exact characterization in all degrees.

## Correct cost model

AND gates are unlimited and free for this statement. Normalize every costly OR gate into the OR of two arbitrary conjunctions of input wires and previous OR outputs. The final output is a conjunction. Any branch whose positive signature is contained in its sibling's can be deleted without losing required positives, while only removing negative errors.

A stronger normalization chooses a nonempty positive signature S for each conjunction, then conjoins every available earlier wire whose positive signature contains S. This leaves the conjunction's positive signature unchanged and can only remove negative errors. Thus each OR joins two closed positive signatures; the final output is the conjunction of all wires true at every required positive sample.

## Local substitution searches

An improvement of a local incidence subgraph by one OR gate embeds into the full plane and refutes the bound. The first structure is an eight-vertex theta graph: take a point x off a line y, and three points a1,a2,a3 on y, with b_i the line joining x to a_i. It has nine incidence edges, hence the standard circuit uses eight ORs. Searching seven ORs would save one globally.

The local variable order `[x,a1,a2,a3,y,b1,b2,b3]` is the global input list `[2,0,1,3,13,25,14,15]`. It has thirteen maximal projected negative samples. Exactly four local assignment masks are free: 14,15,224,240; these are the two pure triples and their extension by the opposite endpoint. Monotonicity leaves nine admissible local truth tables. Data are in `/tmp/oec/pequalnp-pilot-62/theta-truth.json`.

A second structure consists of a quadrangle's four points and its six joining lines, with twelve incidence edges. Its local graph has fourteen maximal negative samples. A ten-OR realization would improve the usual eleven.

Z3 5.3.3 was fetched from its public GitHub release and is usable with `PYTHONPATH=/tmp/oec/pequalnp-pilot-62/z3-python`. The scripts `or_synthesis.py` and `or_closure_synthesis.py` are in task scratch. The initial seven-OR theta and ten-OR quadrangle runs each returned `unknown` at 120 seconds. They establish no lower bound. The closure-normalized theta seven-OR search likewise returned `unknown` at 180 seconds. As a control, eight ORs gave SAT in 1.9 seconds, computing exactly the ordinary nine-edge theta function, with no cubic slack used.

## Further routes

- Full theta4 uses a point off a line and all four points on that line, with the four joining lines. Its twelve edges have a standard eleven-OR circuit. Searching ten ORs with both sets of pure triples allowed returned `unknown` at 600 seconds; the projected negative family has nineteen maxima.
- A quadrangle twelve-edge circuit using eleven ORs could still save globally if it makes available an OR of opposite joining-line variables. Their intersection point is outside the quadrangle. Multiplying that shared wire by the outside point variable adds two incidence edges for zero ORs; one outer join would then give fourteen edges with twelve ORs. The forced-first-OR test uses local inputs 4 and 6, global line variables 13 and 15. The exact local data are in `quadrangle-truth.json`. This SAT query returned `unknown` at 300 seconds.
- Symmetry splitting of the theta first OR includes nonlinear initial edge monomials. Its seventeen useful free-AND closures produce 118 incomparable operand pairs, grouped into eighteen orbits under branch permutations and duality. `theta_orbits.py` checks that these actions preserve all maximal negative samples. Representatives are in `theta-orbits.json`.

## Pair-only controls

The stronger conjecture that a C4-free quadratic shadow alone forces `edges - 1` OR gates survives two exact SAT controls (not Lean proofs): C5 with three ORs is UNSAT in 0.088 seconds; C6 with four ORs is UNSAT in 0.144 seconds. Only incorrect pairs are forced false in these controls, so arbitrary higher-degree slack is allowed. Logs are `or-cycle5-3.log` and `or-cycle6-4.log`.

The geometry agent owns the analogous theta pair-only test, using the installed Lean CaDiCaL binary after CNF conversion. Avoid duplicating that search.

A bowtie (two triangles sharing one vertex, six edges, no four-cycle) likewise cannot use four ORs in the finite model: UNSAT in 0.35 seconds. Singletons must explicitly be required false when a vertex has no nonneighbor. As a positive control, a four-cycle does admit two ORs, found by the same encoder.

## Latest status, 2026-11-25 03:33 UTC

The smaller reusable-wire test uses an exact C8 on four quadrangle points and four cycle lines. It has eight positive edges and ten maximal negatives, with no cubic slack. Seven ORs containing an OR of opposite point variables could cover two outside incidences at the cost of one final join. The forced reuse test with the rigorous per-negative sensitivity cuts returned `unknown` at 180 seconds. Data: `cycle8-reuse-truth.json`; full log: `or-cycle8-reuse-sensitivity.log`.

All of this agent's solver processes have finished. No counterexample was found. The definitive small UNSAT controls are finite SAT-model results, not Lean-checked proofs of any posted statement. The algebraic agent continues independent constructive searches using the exported local data.

Scripts worth preserving from task scratch are `or_synthesis.py`, `or_closure_synthesis.py`, `theta_orbits.py`, and `projection_data.py`. All solver stdout/stderr were retained in full logs. No Lean theorem was produced by this strategy.

## Sustained query started 03:38 UTC

The parent requested a substantially longer exact query. `or_cover_cadical.py` adds a rigorously necessary dynamic cut: after any prefix, the positive signatures of current wires false on a fixed negative row must admit a cover of all required positives of size at most one plus the number of remaining OR gates that are false on that row. A new false OR can lower the covering number by at most one; a free conjunction cannot lower it.

The enhanced encoding preserves named signature bits through CNF conversion. Both a two-OR C4 witness and the known eight-OR theta witness are reconstructed and independently simulated successfully with every cut enabled. The live 900-second CaDiCaL query is theta3 with seven OR gates, all thirteen generic negative maxima, all eighteen first-OR representatives, static sensitivity cuts, and 78 prefix cover cuts. Its tag is `theta-seven-cover900`.

Search scripts, datasets, complete completed-run logs, and the live query's SMT/CNF/mapping/command are archived under `results/orch/search-counterexample/`, with `SHA256SUMS`. The current running solver log will be copied when the process ends.

At 03:49 UTC the query returned **UNSAT**, with CaDiCaL exit20 after650.79seconds wall time and590.51CPU seconds, using70.17MB. This rules out the seven-OR local witness in the encoded canonical model; it is not a Lean proof of the global posted statement. No separate UNSAT proof certificate was generated. The complete artifacts are archived, including the original formula, CNF, mapping, solver command, full log and outcome.

`results/orch/lemmas/CounterexampleClosure.lean` then compiled successfully with exit0 and empty complete build log. Its two helper lemmas check the positive-sample closure argument and the finite-cover replacement inequality. They do not establish all encoding completeness steps or the posted theorem.

## Multi-output route

`multi-output-line-neighborhoods.json` specifies a new candidate search over only thirteen line variables. It has thirteen singleton-positive samples, thirteen output target masks (the four lines through each point), 468 cap-negative samples, and126 relevant negative rows per target. Each target output is the free-AND closure of available wires whose singleton signature contains that target mask. A shared38-OR family would give a global50-OR counterexample after multiplication by point variables and twelve outer joins.

`multi-output-baseline39.json` is the ordinary39-OR, thirteen-output construction, independently simulated on all8192line assignments. It is a control, not a saving. The algebraic beam agent is assessing this new search. No worker is currently running under this agent after the completed CaDiCaL run and helper check.

## Multi-output results, 2026-11-25 04:17 UTC

Independent audit approved the canonical multi-output encoding and its targetwise pruning from468 original negatives to234 maximal four-line caps. The thirteen-output39-OR control passes all7280 output/cap checks. The full38-OR query failed during Z3 bit-blasting at the explicit3GiB memory ceiling, before a solver run; this establishes no lower bound.

Three collinear outputs (points0,1,3; ten line inputs,27 projected negative maxima) are UNSAT with eight ORs in12.76seconds. Three noncollinear outputs (points0,1,2; nine line inputs,15 negative maxima) are UNSAT with eight ORs in9.17seconds. Nine-OR controls passed and reconstructed their witnesses. These are finite model results, not Lean-checked lower bounds. The four-cap module (points0,1,2,5; ten inputs,28 negative maxima) has a verified twelve-OR control and a live eleven-OR900-second query.

The pure-union DAG specialization is implemented in `union_dag_search.cpp`: every paid gate unions two earlier line masks, and each output freely intersects all available masks containing its required pencil. Its39-OR control passed independent Python evaluation against all original generic rows and all560 cap assignments. A one-second smoke search explored440,569 mutations with no38-OR witness; its best candidate still missed one pencil. The heuristic score is an exact four-element covering potential, not a lower-bound proof.

Completed artifacts are immutable in `search-counterexample/batch-20261125T0417Z/`, with their own SHA256 manifest. A direct streaming CNF implementation is being validated to avoid Z3 conversion overhead on the full model.

## Full-model query, 2026-11-25 04:29 UTC

The four-cap eleven-OR query ended UNKNOWN at900.423seconds; its complete finished artifacts are in `batch-20261125T0429Z`. This establishes no lower bound.

The direct streaming encoder avoids the Z3 conversion bottleneck: full39-OR control uses about12MB Python memory, gives SAT, and reconstructs a witness passing7280 output/cap checks. Independent review tested1068 CNF primitive truth cases and the finite witnesses. Two-output five-OR control is UNSAT. The unstrengthened triangle eight-OR query timed out at30seconds.

A separately reviewed late-prefix cover cut selects current false wires covering the union of targets required false at a negative row. Their number is at most the number of false outputs plus the remaining false OR gates. Reverse elimination of future OR gates proves this necessary condition. The finite counter was independently checked on4608 Boolean cases. With the cut, triangle eight-OR is UNSAT in40.815seconds; full39 and pair-five controls still pass.

At04:29UTC the full thirteen-output38-OR query launched with one prefix cut at gate35,745242 variables and2722655 clauses, a900-second CaDiCaL wall limit and3GiB inherited address-space cap. Its source, prepared CNF and controls were archived before launch in `batch-20261125T0428Z`. The finite model remains a restricted line-output architecture and is not equivalent to arbitrary26-input circuits.

An alternative exact pure-union model (final free intersections, each paid gate unions two prior masks) has31542 variables and357605 clauses at38 ORs; its39-OR control passes7280 checks. It is prepared as a fallback, not yet queried. The direct base and pure-union inputs/controls are preserved in `batch-20261125T0422Z`.

## Interrupted query recovery, 2026-11-25 04:46 UTC

The execution environment briefly reinitialized before the full38 query completed. Its old CaDiCaL PID20190 was recovered as a zombie with wait status9, hence SIGKILL, after638.8 CPU seconds. Both surviving logs have no SAT/UNSAT verdict, and the old unified-exec session is unavailable. The precise SIGKILL cause is not established. The run is **interrupted**, not UNSAT and not a completed timeout. Complete surviving logs, exact command, raw process status and recovery metadata are immutable in `batch-20261125T0446Z`; hashes verify that the original CNF and mapping match their previously archived copies.

Two alternatives are prepared and independently reviewed: an arbitrary26-input50-OR canonical model with8 first-gate symmetry orbits, and a strengthened ten-OR theta4 model with18 first-gate orbits and late-prefix cover cuts. No large arbitrary-circuit query has run yet. The theta4 eleven-OR control passes every forced assignment among all1024 local assignments. The arbitrary51-OR baseline was independently evaluated on all520 prescribed samples, but its large CNF control has not yet run.

## Global controls and guarded restart, 2026-11-25 05:35 UTC

The strengthened theta4 ten-OR query ended UNKNOWN at900.147seconds, with its complete input and output preserved in `batch-20261125T0504Z`. No witness or lower-bound conclusion follows from that timeout.

The arbitrary-circuit encoder now includes26 redundant singleton negatives and a necessary singleton-dirty OR clause, justified by the checked clean-OR theorem. Its optional late-prefix cover cuts are imposed on36 cyclic representatives; all468 original generic negatives remain. The forced51-OR global control returned SAT in12.40seconds and reconstructed a witness satisfying all546 samples. This validates the control and decoder, not the existence of a50-OR separator. The full input and assignment are preserved in `batch-20261125T0509Z`.

The first unrestricted50-OR attempt was explicitly stopped by SIGINT to protect a concurrent Lean build at the shared memory ceiling. Its result is UNKNOWN, exit−2,76.08seconds wall time and2,081,132KiB peak child memory. The complete input, mapping, output and stop metadata are preserved in `batch-20261125T0512Z`. The212MB raw CNF was reclaimed only after verifying its SHA256 against the compressed archived copy; restarts reuse that copy and hash rather than duplicating it.

A guarded runner verifies the decompressed CNF hash, streams it to CaDiCaL's documented stdin interface, tracks its owned process group and reader, and stops its own children if shared memory reaches6.5GiB. It applies a3GiB address-space ceiling and a4GiB startup guard. Its two-OR C4 smoke passed SAT with a clean reader exit and reconstructed all six samples. The primary global50 query restarted at05:34:27UTC after all Lean jobs finished, with a900-second limit and this guard. It is still running at the time of this note.

A smaller seeded-repair encoder fixes most positive operand signatures of the51-OR baseline and permits selected neighborhoods to change after one gate is deleted. Its finite search scope is explicitly restricted. Independent review approved Boolean-constant handling, attainable closure constraints, and disabling the global first-OR symmetry restriction for fixed neighborhoods. The fully fixed51 control passed SAT in0.255seconds and reconstructed all546 samples. The five-free-gate control and eight-free-gate50-OR repair query are prepared; they have not run yet.

The pure-union38 fallback has been deprioritized because two agents independently audited a mathematical lower bound of39 for binary union gates with final free intersections. That argument is not yet Lean-certified and does not apply to the arbitrary free-AND model. The canonical thirteen-output38-OR query remains a possible restricted counterexample route.

The proof agent has now checked a generic canonical-program compiler, fixed520-sample masks, a51-OR control mask certificate, and the conditional wrapper deriving the literal posted negation from an actual≤50 witness. The geometry completeness certificates also passed. No actual≤50 witness has been found. These checked preparations make a future candidate quick to verify; they are not a refutation by themselves.

## Completed bounded queries and current primary, 2026-11-25 06:22 UTC

The guarded unrestricted50-OR query completed its full900seconds with UNKNOWN, exit0, and no resource stop. Final statistics include361675conflicts and4561943decisions. Complete evidence is in batch0549. A continuous3600-second run of the same original input began around05:51UTC. Its terminal status was discovered at06:25UTC: it had failed after1819.61seconds with std::bad_alloc and SIGABRT (exit−6) under the3GiB address-space ceiling. This is UNKNOWN due to resource failure, not a completed3600-second timeout. No simplified-CNF or extension export was produced. Batch0627 preserves the entire output and explicit status.

The nine-free-slot repair of the original51-OR seed likewise returned UNKNOWN after900seconds; batch0553 preserves its complete output. Imported-seed handling now replays every source program before pinning signatures. The nonlinear51 control is a different circuit shape but computes exactly the original52-edge incidence function, as confirmed by symbolic DNF expansion. A local deletion diagnostic found no50-OR result. Its original scope was nonempty replacement conjunctions; an independent constant-true replay also failed at all51 deletions, preserved in batch0553.

The proof agent supplied an INVALID48-OR projective-coordinate marginal circuit. Independent replay confirms all52 incidence positives and all352 assignments of weight at most two, but it fails378 of the468 required generic negatives. Thus it gives a concrete q=3 obstruction to quadratic-shadow-only lower bounds, not a refutation of the posted statement. Batch0557 preserves this seed, the explicit invalid-seed loader, and controls. Freeing W/E gates24–32 plus two extra OR slots48–49 produced a50-gate template; its full900-second query returned UNKNOWN. Complete outcome: batch0611.

A reviewed counterexample-guided loop preserves the pinned template, every original row ID, all candidate programs, full468-row verification, source/dependency hashes and reproduction recipes. Its first run on eight spread failing rows returned UNKNOWN after120seconds. A calibrated run starts with eight rows already rejected by the seed. It found a sampled50-OR SAT program after48.16seconds, but full verification found396 generic failures and16 incorrect quadratic pairs. After adding three failed rows, the next round returned UNKNOWN. Both are explicitly invalid/unfinished results.

All90 generic rows already rejected by the marginal seed cover261 of273 nonedge pairs. A greedy cover of37 rows was reduced to31 by verified removals and two-for-one replacements. The12 uncovered pairs are six point-point pairs involving input1 and six line-line pairs involving input13. Consequently31 known-good generic rows plus12 explicit pair negatives would preserve the complete quadratic shadow while retaining a known feasible initial seed. This is a candidate next refinement calibration, not a result.

A separate unrestricted ordering cut is independently reviewed: after fixing the first OR, adjacent independent gates can be sorted by their output-positive masks. Swapping an inversion leaves the moved-earlier gate unchanged and strengthens the moved-later gate's canonical conjunctions, preserving positives and decreasing negatives. The comparator passed512 exhaustive three-bit cases. Stepwise finite replay checked207 swaps for the valid51 control and179 for the invalid48 seed, with errors remaining0 and378 respectively. An additive CNF packaging is prepared so the ordered global model can reuse the single archived213MB input plus a1.44MB delta, preserving original signature variable IDs. No ordered-model solver query has run yet.

## Ordered restart and four-cap local separator, 2026-11-25 06:39 UTC

The additive ordering package passed an independent complete stream audit:17,672 fresh variables and62,760 clauses are appended to the original global input, preserving all original signature IDs. Both sealed controls passed (C4 two-OR SAT and C5 three-OR UNSAT). The parent approved a sole1800-second ordered global run with4GiB address-space cap after a short serial Lean window; it has not launched yet. Optional simplified exports will remain disabled to protect limited disk space. Frozen batches0625/0627/0628 passed independent review.

A new four-cap projected-row separator uses points0,1,2,5 and their10 incident lines, hence14 inputs and16 positive incidence pairs. Projection of every original generic negative produces222 distinct masks and83 maximal masks. These constraints permit22 pure-line cubic minterms in addition to16 required quadratic minterms; they do not specify the exact local incidence function. A14-OR witness would embed into the full26-input problem by adding36 remaining edge joins, giving50 ORs, and would require full original-row replay. The earlier four-cap11-OR query was a different multi-output architecture; theta3/theta4 and the quadrangle core also differ.

All24 permutations of the four cap points act on the local graph and preserve its83 negative maxima. There are26 distinct nonempty initial signatures,297 incomparable first-OR pairs and22 symmetry orbits. The staged14-OR model has71,825 variables and260,419 clauses, including sensitivity and final-three cover cuts. Its15-OR DNF control is also staged. Independent adapter/data review is pending, and no local solver has launched.

## Live ordered/local searches and next multi-output cut, 2026-11-25 06:53 UTC

The reviewed ordered unrestricted50-OR query launched06:40:27UTC, PID34856, for1800seconds with4GiB address-space cap and6.5GiB shared guard. The verified composition reuses the archived original input plus its ordering delta; optional exports are disabled. It remains running without a verdict.

The four-cap15-OR solver control passed SAT in0.252seconds, and independent audits verified all16,384 local forced assignments plus547 embedded global checks. Its14-OR query launched06:44:07UTC, PID35170, for900seconds with1GiB cap and5.5GiB shared guard. It remains running. Reviewed control/data/prepared-input artifacts are frozen in batch0644.

The three-collinear-pencils separator is also new: points0,1,3 and10 incident lines yield13 inputs,12 required edges,81 maximal projected negatives and22 allowed cubic minterms. Its108 geometric symmetries produce10 first-OR pair orbits. The11-OR control passed SAT in0.254seconds and embeds by40 edge joins into51 ORs; all8192 local assignments and547 global checks pass. The10-OR query is staged for the next secondary slot. Source/data/control evidence is frozen in batch0647.

For the older13-output38-OR model, checked active-target guard charging implies some OR singleton support must equal a pencil. Restricting to guards false on a four-cap strengthens this to a useful exact-pencil gate. A Singer rotation fixes its pencil toP0, and first-gate symmetry is reduced to the point-zero stabilizer to avoid incompatible normalization. Separate simple/useful source variants passed independent mathematical and finite-data audits, preserved in batch0650. No result for that38 model is claimed.

The same adjacent-independent ordering cut is being combined with the useful-pencil model, preserving all singleton signatures and decreasing cap values. One combined39-OR control input has been generated; review and bounded runtime control are pending. The earlier unordered control input was never solved, and its raw57MB was reclaimed after retaining its exact hash/source/recipe, mapping and complete encoding log.

## STOP: lease lost, 2026-11-25 06:59 UTC

Root reported HTTP410 from renewal and its diagnostic retry and instructed immediate stop. Both owned solver groups received verified-identity SIGINT at06:59:01.933UTC and are fully reaped. Ordered global50 is UNKNOWN/exit−2 after1114.838seconds; cap4 local14 is UNKNOWN/exit−2 after894.274seconds. Neither completed its intended limit, and neither produced a witness. Full output and separate external lease-loss stop records are frozen in batch0659. The collinear10 query never launched.

The one-useful-pencil plus ordering39 control passed SAT in6.346seconds and is fully preserved in batch0654. A later two-distinct-useful-pencil source variant passed independent mathematical/encoding review, and its forced39 CNF generation completed before stop; no solver ran on that new input. All source/input/mapping/encode logs are frozen in batch0659. No active search or Lean work remains under this agent. No full51-OR proof or valid≤50 global counterexample was found.
