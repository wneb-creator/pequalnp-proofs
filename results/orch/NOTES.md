# pilot-84: L-meta-9502

Sole lease held by root. Assigned 2026-11-25 11:22:02 UTC after eight nulls.
Exact desk data and statement: /tmp/oec/pequalnp-pilot-84/desk-response-9.json and statement.txt.
Target: no <=71 gate AND/OR representation of CYCLE_11 (33x33); a checked counterexample also counts.
Final file: lean/PEqualNP/Outside/L_meta_9502.lean.
Imports allowed: PEqualNP.Defs, Mathlib modules. All helpers own namespace, final fully named theorem last.
Setup agent owns cache: wait for its ready signal before any lake build; no Mathlib source builds.
Use /tmp/oec/pequalnp-pilot-84/lean-env.sh. Full checker cache currently constrained by disk.

Strategies: status_audit lower bound; circuit_search computational witness; representation_strategy hand decomposition; root integration/Lean encoding.

Append findings with UTC timestamps below.

[2026-11-25T11:24:14.340602+00:00] status_audit
## Lower-bound audit
- Existing RepReads.reads_le proves forced input count ≤ size + 1. This graph forces all 66 inputs, yielding size ≥ 65.
- RepPath.path strengthens by one gate when an induced four-vertex path occurs, yielding size ≥ 66 here.
- RepInduced.induced preserves excess of induced subgraphs relative to forced inputs; no available result yet forces the required excess 6.
- The undirected graph is a cyclic chain of 11 bicliques {A_i,B_i} × {A_(i+1),C_i}, sharing A vertices. Straight merge of left/right vertex wires costs 33 + 22 + 11 + 10 = 76 gates.
- Existing exhaustive lower-bound files (e.g. L_meta_6381, L_meta_8299) use finite live-wire search; direct use at 71 gates appears infeasible.

- 2026-11-25T11:25:48.362515+00:00 certificate: Positive witness pattern found in L_meta_9103/9099: raw Circuit lists, Monotone2 via simp, Represents by decide +kernel. Generated independent76gate baseline (33 side-pair ORs, 11 K22 terms, OR aggregation), checked all1089inputs in Python; Lean compile pending rootbeat. Scratch certificate/Baseline76.lean and baseline76.json.
- 2026-11-25T11:25:48.362515+00:00 submission: outside-guard checkGap uses posted row kind; authoritative rejects arbitrary refute on check rows.9502 negative statement currently check; its positive twin9501 is separate. Root informed; preserve refutation results if found before resolving delivery.

[2026-11-25T11:29:21.232371+00:00] status_audit CORRECTION: A proposed bound size >= forcedInputs + number of induced disconnected P4 components - 1 is FALSE for representing circuits. The symmetric double-cover of an undirected P4 has two disconnected P4 components but an8gate circuit (4 coordinate-merging OR gates +4 P4 edge gates), below the proposed9. Same-side pairs are unconstrained, so opposite-side twins can merge and duplicate obstructions. Do not formalize this unpolarized packing invariant.

- 2026-11-25T11:29:25.212665+00:00 row_graph: RowGraph.lean compiled successfully (exit0, no diagnostics). Kernel proof adjRows_correct verifies33 explicit row masks against exact desk adjacency for all1089pairs via decide +kernel. Scratch certificate/row-graph/RowGraph.lean; validation.txt records observed20.75s walltime including polling/reportinglag. Largest mask4296016385 (10digits). No raw circuit evaluation in this lemma.

- 2026-11-25T11:30:53.643862+00:00 certificate: Raw baseline76 full1089-evaluation decide +kernel exited137 with emptylogs (likely memory kill). Fast reflection route now kernel-checked: certificate/RowProto.lean proves row_circuit_sound for arbitrary raw2-inputAND/OR gate lists via33-bit row evaluation; exit0, emptydiagnostics. Independent child row_graph checked33 adjacency masks/all1089bits in RowGraph.lean. Combined Baseline76Rows.lean generated; awaiting pre-long-build beat.

### 2026-11-25T11:32:59.666929+00:00 representation_strategy
Graph structure:11 undirected K2,2 blocks {A_i,B_i}×{A_(i+1),C_i}; bipartite representation matrix is the double cover, a necklace of22 squares. Standard76gate construction:33 coordinate ORmerges,22 block-side ORs,11 ANDs,10 final ORs.
Simple pairedrectangle route cannot improve76:22 oriented K2,2 terms cost87 before sharing; only22 mainA copies repeat, so commonlinearORpair sharing saves at most11. Nonlinear intersections or a substantially different decomposition are needed.
Potential lowerbound parameter:66 forced inputwires gives65 connectedfan-in2 lowerbound. At≤71gates the connectedDAG has≤6fanout surplus. Baseline has11 surplus from reused maincoordinate ORmerges. Proving at least7 surplus would settle9502, but no formal theorem established.
Smallgadget direction shared with circuit_search: path3 after2 endpair ORs has8 effectivevariables and target P(c∨d)∨(c∨e)(f∨g)∨Q(f∨h); baseline9 moregates, would need≤8 to save1. Path2 weight≤2 supportgadget needs7gates; circuit_search reports6gateSATUNSAT (diagnostic only).

2026-11-25T11:33:24.195648+00:00 circuit_search: Constructed76gatebaseline and independently verifiedall1089pairinputs (scratchcircuit-search/baseline76.json). Globalpromise-care single-gateresubstitution5minfoundnoimprovement. BundledCaDiCaL discovered in Leanbin. ExactCNFsearch: z-spacepath2≤6gatesUNSAT; z-spacepath3≤10UNSAT; compressedpath3eightvars≤8UNSAT; directpath2with2endpointzinputs≤11internalgatesUNSAT. Thesearecomputationaldiagnostics, notLeanproofs. Directpath3target18internalgates andsmallcycle3/4searchesunderway.

- 2026-11-25T11:33:29.022754+00:00 certificate: FULL76GATEUPPERPARTIAL KERNELCHECKED. certificate/Baseline76Rows.lean compiledexit0; outputlogs empty. Genericrowreflection+adjacencymasks+33evaluatedrows prove RepSizeAtMost adjGraph76. Does NOT proveassignednegative71statement or refuteit. Rootinformedimmediatelyforearlypushafterreview.

- 2026-11-25T11:33:41.121835+00:00 row_graph: TraceProto.lean compiled exit0 with generic rowValue, traceCheck, trace_correct. The checker compares each provided gate result against rowValue then appends that provided value; soundness identifies full foldl with inputs++providedOutputs. This avoids repeated nested computed-gate expressions if needed. Full76trace benchmark cancelled because parent direct33row certificate passed; no active child process.

[2026-11-25T11:33:54.904728+00:00] status_audit: Lower66.lean compiles cleanly: all66inputs forced plus the induced path rows0,2/columns1,22 proves size>=66. WithInduced.lean additionally ports induced restriction/excess transfer and compiles. Existing finite obstruction13124385 embeds exactly at rows[21,24,1,15,29,6], cols[0,2,5,7], offering a route to>=67. FiniteLower.lean is benchmarking the accepted source with only PEqualNP.Defs imported; current subprocess23620.

### 2026-11-25T11:42:22.929705+00:00 representation_strategy checked structure
ElevenPaths.lean compiled with exit0 and no diagnostics. It proves the induced11P5 structure explicitly: delete right main vertices0..10; component i is B_L,i–C_R,i–A_L,i–B_R,i−1–C_L,i−1. Physical-mask and typed33×22 embedding identities are checked by kernel reduction, as are injection properties. Source is scratch representation-strategy/ElevenPaths.lean.
Reflection pairing experiment: merge L_v∨R_{π(v)} for a graph reflection. Four axis vertices must remain unmerged because v is adjacent toπ(v), leaving29 merges and37 signals. Result has52 graph edges. Exact MILP weighted biclique-cover optimum is49 graph gates, total78: this simple reflected construction is worse than identity76. Complete calculation logs and graph/covers are in representation-strategy/.

[2026-11-25T11:44:21.345629+00:00] status_audit IMPORTANT CORRECTION: L_meta_8299 is merged (27167057, PR12886), but its public authoritative comments both report FAULT exit124, not ACCEPTED. Calling its finite certificate accepted was unsupported. Our67bound remains unproved until local kernel/checker succeeds. Full copied certificate OOMs; front_small removed using10unique separating probes; currently testing45singlepairchunks single-threaded.

[2026-11-25T11:51:46.205045+00:00] status_audit: Lower67.lean COMPILED exit0 with empty Lower67-1.log (1981lines). P7 matrix2457(4x3) no<=7gate certificate checked bykernel; embedding rows[0,2,4,6], cols[1,3,5] and induced excess transfer proves lower67 forleasedgraph. This is partial only; targetrequires72. Smaller P7certificate replaced unwieldy10-input2P5 source. Allhelper imports onlyPEqualNP.Defs.

### 2026-11-25T12:01:18.899695+00:00 circuit_search: row-bound conjecture refuted
Explicit 10-gate circuit for a 6×3 matrix with row masks [1,2,4,6,5,3]. All six rows are distinct, nonempty and proper; all three columns are nonempty and proper. This disproves the proposed universal bound size≥2*numberOfRows−1 even under the strengthened column hypotheses. Verified all18 oneEach inputs in Python; certificate agent is kernel-checking. Raw gate list: /tmp/oec/pequalnp-pilot-84/circuit-search/row-bound-counterexample10.json. Construction uses three merges of complement-row inputs with matching column inputs, then a7-gate partial-net circuit. This is an auxiliary conjecture counterexample, not a refutation of L-meta-9502.
Small SAT diagnostics: existential row-bound counterexamples for n4,m3,size6 and n5,m3,size7–8 are UNSAT; n6,m4,size9 UNSAT, size10 timed out. P7 incidence matrix size7 is UNSAT in the minimal-circuit encoding. Larger P5/path searches timed out and establish no lower bound.
