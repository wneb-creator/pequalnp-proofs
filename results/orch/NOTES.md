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
