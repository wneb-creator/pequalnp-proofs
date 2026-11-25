# L-meta-2592 orchestration notes

Held only by root pilot-95. Exact statement: scratch desk-next.json.
Only allowed project module: PEqualNP.Defs.
Existing reductions occupy all three slots.


- 2026-11-25T13:48:08.453466+00:00 reductions: cap saturated by 2592_271/_318/_408. Checked L_meta_4725 gives 15 + NOT-count <= size (>=5 NOT impossible). Checked L_meta_5236 gives >=16 binary gates for Petersen with supplied x0 OR x2, excluding >=3 NOT in 18-gate remainder. Details: lemmas/reductions.md.

2026-11-25T13:48:15.556907+00:00 proof_route: existing 15+NOT floor found (L_meta_4725); 9-input cofactor >15 bound found embedded in L_meta_9818. Missing bridge is ≥4 gate elimination under some restriction. Details in lemmas/proof-route.md.

2026-11-25T13:49:26.869316+00:00 Counterexample: no semantic loophole; two bitparallel 19-gate searches running, best initial discrepancy 9/1024. SAT/CEGIS child compiling CaDiCaL.

2026-11-25T13:52:00.779612+00:00 SAT route: CaDiCaL+CEGIS built; planted20 passes all1024 inputs. Four-gate-change neighborhood around four-error19 candidate UNSAT; larger/relocated-NOT neighborhoods and general first-NOT shard pending. No counterexample.

- 2026-11-25T13:52:01.949944+00:00 reductions: proposed stronger partial Sixteen.lean gives 16+NOTcount<=size by running L5236 signed certificate on the original ten pins; root Defs build pending. If compiled, this excludes all >=4 NOT circuits, leaving 1..3. Exact normalization component is already L7389.

2026-11-25T13:54:02.851971+00:00 proof_route: Restriction.lean compiled successfully (Defs only). kept_projection_bound converts a retained input made constant after the first binary gate into an extra gate lower bound. Generic lower L on a cofactor yields L+1≤tail gates, hence≥17 when L=15. Arbitrary-vertex projections and twin obstruction will combine.

- 2026-11-25T13:55:37.908728+00:00 reductions: Normalization.lean compiled successfully (exit0; only deprecation/unused-simp warnings) and independent status_review passed. Sixteen.lean certificate compile progressing without errors; reviewer verified source derivation and all1024 target assignments. Stronger realizeOrdinaryPins variant in scratch preserves raw pins for proof_route seventeen-binary-gate strategy.

2026-11-25T13:56:06.363586+00:00 proof_route: strengthened generic lemma to kept_projection_charge, compiled exit0. Bound now L+1+cost(projected first gate)≤tail gates; if firstgate becomes constant, gain two charges and binary≥18. Updated Restriction.lean and logs.
2026-11-25T13:57:11.741079+00:00 not_cases: BOTH first binary inputs must survive into tail; TwinBothLight Lean exit0. Fragment ready, proof_route integrating binary>=17. First non-OR might yield>=18.

2026-11-25T13:58:33.277410+00:00 proof_route: Projection.lean compiled exit0, no warnings. Kernel checked ten vertex automorphisms and all 512-bit cofactor tables. pin_projection maps any chosen Petersen inputfalse to the existing9-input certificate and supplies allotherpins freely. Assembly of≥17 underway.

2026-11-25T13:59:01.383991+00:00 Counterexample: fixed8gate fourORbase +3gates structured route exhausted (17,860,500 checks), no witness. Freer6input vector SAT ongoing.

- 2026-11-25T13:59:53.440308+00:00 reductions: Sixteen.lean COMPILED exit0. Proven sixteen_binary:16+NOTcount<=size for ordinary Petersen; four_not_impossible excludes>=4NOT at19. Source285KB independently audited PASS. Root notified for immediatepush. Strongpins variant prepared for next17-bound strategy.

2026-11-25T14:02:01.249139+00:00 SAT: conditional6input5output11gate vector (A,B,C,D,N), D∧N=M, exactlyoneNOT, firstOR(a,b) UNSAT in60s; unrestrictedfirstgate nowrunning. No witness.

2026-11-25T14:02:10.569366+00:00 Root: rejected generic duplicate-wire charging. Signed multiplexer with duplicate raw input uses 3 gates without a saving; monotone majority with roots [a,b,b,c] uses 4 gates, matching its optimum. Only constant-wire charge is sound without graph-specific hypotheses.

2026-11-25T14:02:10.569366+00:00 Root read https://pequalnp.com/papers/note-1 (dated 2026-11-24). Its general edge-function lower bound requires separated hubs/long cycles, so does not cover Petersen. No new full-bound result obtained from paper.
2026-11-25T14:05:12.950787+00:00 not_cases: OverlapLight Lean exit0. TwoORs(a∨b),(a∨c) require raw a ifb,c nonadjacent; adjacentcase masksunderedge bc and cannotbeexcludedbyretention.

2026-11-25T14:06:09.578275+00:00 20-minute replan: retain signed lower-bound assembly (17 binary globally,18 for non-OR firstgate); target OR-first structural pruning with actualNOT-count tracking via L7227/L6060. Continue six-input multi-output counterexample search to budget; then test signed18 with freeNOTs to find ceiling of genericbinary approach. Drop genericduplicate-charge and naiveper-gate-star normalization, both have counterexamples. Fullposted theorem still unproved; allcompiledcomponents arebeing preserved on pilot95.

2026-11-25T14:06:12.370156+00:00 status_review: naive monotone star-normalization route blocked. Checked L_meta_4849 has a minimum 11-gate circuit for an 8-vertex triangle/C4-free graph, with an AND producing nonedge {2,7} that later gates filter out. Independently verified all 256 assignments, tau=4, m+tau-1=11. Thus the desired bound is not refuted, but every-AND-biclique-inside-G is false even for minimum circuits. R_meta_5375_41 isolates a genuine missing repair hypothesis. Exhaustive monotone circuit enumeration through 4 gates found no violation for all 53 nonempty C4-free labeled graphs on 4 vertices; computational evidence only.

Tool paths: PATH prefix /tmp/oec/pequalnp-pilot-95/toolchain/lean-4.36.0-linux/bin. Checker requires PEQUALNP_REAL_LAKE=/tmp/oec/pequalnp-pilot-95/toolchain/lean-4.36.0-linux/bin/lake and PEQUALNP_HOME=/tmp/oec/pequalnp-pilot-95/toolchain/build-queue. Pinned cache complete; never lake update or source-build Mathlib.

2026-11-25T14:16:00.347285+00:00 Counterexample sanity: Twenty.lean compiled successfully (known 20-gate upper bound). No 19-gate witness.

- 2026-11-25T14:19:31.015131+00:00 reductions: TerminalNot (soleNOTatoutput impossible) andTerminalTwo (twoNOTterminal sandwich collapses to monotoneprefix) compiled. CorrectedExtensionsPublic.olean cache also compiled with17binary andnonOR18 hardlogic. ActualtwoNOTcircuitdecomposition inTerminalStructural under test; rootproof_route seekingmonotone18 toclosecase.

- 2026-11-25T14:22:35.751181+00:00 not_cases: three centered-OR prefix >=19 binary bound and actual supplied-OR circuit wrapper checked; OR/AND retention certificates checked, mass-two assembly in progress.

2026-11-25T14:24:28.730719+00:00 Signed18 stochastic search ended after3,593,000,000 mutations and17,965 restarts; best remains4false positives,no witness. Signed17 search started.

2026-11-25T14:27:47.103106+00:00 40-minute replan: keep checked global17+NOT bound stable. Build shared signed/monotone nine-input core to obtain monoPetersen18; combine with checked arbitrary-outputNOT extraction (saves2gates) to close NOT-output cases. Pursue constantNOT feeding finalbinary with signature extraction, not a large rewiring compiler. Search priority shifts to common-t second independent-triple architecture; cap generic signed search and switch when new search ready. Remaining main cases1/2NOT with AND/OR output remain unresolved.

2026-11-25T14:28:11+00:00 proof_route: MonoPublic checked: nine-variable monotone floor16 implies Petersen monotone18 by first-gate retention and restriction. Actual combined nine-variable certificate still compiling. ConstantNot checked: semantically constant NOT gates can be extracted in monotone mode at zero cost; compiler avoids physical circuit rewiring. Both scratch tests imported cached named Seventeen; flattened fragments rely on its source helpers. Logs empty.
