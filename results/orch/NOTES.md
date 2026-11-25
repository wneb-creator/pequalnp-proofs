# Current task: L-meta-2590, Petersen monotone19 lower bound

Lease returned by recovery request; root owns desk calls. Exact statement /tmp/oec/pequalnp-pilot-143/statement-2590.txt. Reductions_open true but reductions_live=3 (cap already reached). New scratch work under results/orch/petersen/. Previous plane work below is archived and stopped.

# Current status: stopped after lost lease; partial only

The named module compiles, but has no theorem proving the posted gap. Local checker: REJECTED (no-theorem). All searches stopped; no full proof or refutation. Earlier progress entries below are historical.

# L-meta-2583 orchestration notes

Assigned statement and lease metadata are in /tmp/oec/pequalnp-pilot-143/desk-next-1.json. Reductions are closed. Only root makes desk calls or pushes. Each agent writes a distinct notes file and scratch Lean files under results/orch/lemmas; root alone edits the final named proof file.

2026-11-25T14:56:28.917266+00:00 library_route: Found checked full read1 star builder L_meta_7684; preparing plane specialization. Sharp unrestricted AO2 lower bound remains unresolved.

2026-11-25T14:57:02.376415+00:00 normal_form: checked Lift preservation and termination exist (4293/4295); residual dirty-AND cost remains unresolved. See normal-form.md.

2026-11-25T14:57:26.113329+00:00 Toolchain: installed pinned Lean v4.36.0; source /tmp/oec/pequalnp-pilot-143/lean-env.sh; initial Mathlib cache download pending.

2026-11-25T14:58:02.535767+00:00 library_route: Prepared library_lower.lean, exact-assumption lower bound 3*N≤size+1 via inlined 2988. Awaiting toolchain/cache.

2026-11-25T14:58:21.641751+00:00 readk_strategy: prepared canonical read1 upper-bound construction in lemmas/readk_star.lean; missing core is unrestricted lower bound N*(q+2)-1. Awaiting cache before compile.

2026-11-25T14:58:33.073990+00:00 Toolchain ready: pinned Lean v4.36.0 installed; lake exe cache get finished exit 0, full Mathlib cache present. Source /tmp/oec/pequalnp-pilot-143/lean-env.sh before commands.
2026-11-25T14:58:52.417401+00:00 counterexample: no weak-incidence loophole found; complete critical assignment sets have 58 (q2) and 756 (q3) elements. Stochastic searches underway for 26-gate Fano / 63-gate q3 circuits. See counterexample.md.

2026-11-25T14:59:21.440755+00:00 readk_strategy: readk_card.lean compiled cleanly (lake env lean, exit0). incidence_edge_card proven. Root notified immediately for reviewed partial push.

2026-11-25T15:01:10.434112+00:00 normal_form: normal_prereq.lean compiles (107 lines): singleton rejection; no input below incidence output; output valid and a gate. Root notified for immediate push.

2026-11-25T15:01:48.889029+00:00 readk_strategy: readk_semantics.lean compiles cleanly; exact prime-implicant characterization proven. Root notified for reviewed push. Pair-vector IsReadK criterion now being checked in separate readk_criterion.lean.

2026-11-25T15:02:02.350511+00:00 readk_strategy: readk_criterion.lean compiled cleanly. IsReadK characterized exactly by per-incidence pair checks, for arbitrary k. Root notified for reviewed push; construction/cardinality and semantics assigned subtasks complete.

2026-11-25T15:02:35.629858+00:00 library_route: 5-variable two-AND exhaustive search supports cover-count conjecture; existing L1006 refutation uses weaker boundary semantics and is not a counterexample to full incidence computation.
2026-11-25T15:03:58.435305+00:00 counterexample: stochastic q2/q3 searches found no witness after 2.60B/231M mutations; complete58-input q2 SAT encoding validated on pinned27-gate witness, now solving26-gate cases (plain and top-form).

2026-11-25T15:06:29.096316+00:00 library_route: library_lower.lean compiled exit0 with exact-assumption 3N bound; five-variable AND/OR count searches saved under results/orch. Both tiny searches found no counterexample.

2026-11-25T15:07:49.302627+00:00 readk_strategy: stopped local-elimination/SAT work immediately on root lease-stop. C6 nonread1 at8gates UNSAT, at9gates verified SAT; computational only. Existing checked criterion stable.

2026-11-25T15:08:03.840088+00:00 normal_form: STOP on root lease-loss instruction. AND-count route incomplete; q2/q3 checked finite bounds found, no general N bound. Final notes saved in normal-form.md; compiled normal_prereq remains unchanged.
2026-11-25T15:08:05.145656+00:00 counterexample STOP on lease loss: no running owned searches; Fano26 unrestricted/TopForm SAT both UNKNOWN after240s, q2/q3 stochastic searches no witness. Full logs saved counter-output/.

2026-11-25T15:08:21.800302+00:00 gate_count_theory: stopped on lost-lease notice; C6 4-OR and Fano19-OR searches found no witness (best1error); no general OR-count proof. Saved notes, source, data, logs.

2026-11-25T15:14:49.785544+00:00 normal_form: New Petersen gap2590. Checked L635 proves AndCount≥6, and L7541 compiles original Monotone2 into OR-free model bounded by original AND count. Inlined/specialized combined scratch normal_and6.lean (2821 lines) now compiling; root notified.

2026-11-25T15:18:52.841921+00:00 Petersen library_route: safeMathlib-tree RUPchecker compiled; OR14 conjecture refuted by20gate13OR7AND witness, kernel verification underway.

2026-11-25T15:22:09.806331+00:00 Petersen gate_count_theory: found and fully truth-table-validated20gate witness13OR+7AND, refuting OR≥14 split; local4gateP5/5gatefullcontext UNSAT with SATpositivecontrols; lower-size search continues.

2026-11-25T15:23:20.856972+00:00 normal_form STOP: Petersen lease lost. normal_and6.lean complete source UNVERIFIED; improved validation pending, initial algebraic bridge needed a recursion-depth increase. Saved detailed caveats in petersen/normal-and6.md.

2026-11-25T15:23:32.000630+00:00 Petersen gate_count_theory: all searches stopped immediately on lost-lease notice (exit130); 12OR/freeAND and13OR/6AND produced no new witness.20gate13OR+7AND result and allsource/CNF/logs preserved.

2026-11-25T15:23:38.109872+00:00 readk_strategy: stopped Petersen work on secondlease-loss; checked readk_bound stable, structuralprobe logs saved.

2026-11-25T15:23:45.766362+00:00 library route: compiledPetersen finite residualcoverprofile library_profile.lean; compiledinlineRUPchecker saved. Witness20 gates external1024checkconfirmed OR13/AND7, finalLeanproofpending whenleasevanished. Child toldstop.
2026-11-25T15:23:56.816565+00:00 counterexample STOP on Petersen lease loss: all owned searches terminated, no19-gate witness; sixSATruns UNKNOWN, threeorderedruns interrupted UNKNOWN. Sources/logs and C6resource UNSAT/LRAT preserved results/orch/petersen/counter-output/.
