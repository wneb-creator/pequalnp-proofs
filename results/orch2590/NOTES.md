# L-meta-2590 orchestration notes

Ownleasea1cdb295-f879-4902-baa7-ce60a1f1590b received15:10:16UTC, expires15:30:16UTC. Exactstatement scratchstatement-2590.txt. MonotonePetersen19 lowerbound. Reductionsopenbut3livecapalreadyfull.
PreviousL2592andL2583leasesunexpected410; allworkpreserved, canreusecheckedhelpersforthisnewgoal.

## Monotone minimization 2026-11-25T15:14:45.152093+00:00

`MonoFirstChecked.lean` clean checked. New namespace L_meta_2590_aux.MonoFirst contains MonoL, elim preservation, drop_core_mono, clean_mono, LeastMono, least_mono, least_mono_first. It minimizes circuit length only among clean monotone circuits; therefore no unsupported transfer from an all-basis minimizer. Nonconstant target not equal to a primary input guarantees first gate exists. The first gate is AND/OR on two distinct primary inputs; repeated input would be an alias removed by drop_core_mono, contradicting monotone minimality. Existing infrastructure is the earlier FirstBinary checked source under L_meta_2592_aux.CircuitProof; new declarations begin after its closing namespace. Full snapshot e40091e655fb4e1ed2362282a601b97bb45338695477775de323a44b8c2e99b1. No remaining proof errors or warnings.

[2026-11-25 15:15:21 UTC, proof_strategy] MonotoneResidualChecked.lean compiled exit0. New restrict_core_mono, restrict_two_drop_mono preserve Monotone2 and bound actual circuit size. residual_rename_mono turns an arbitrary Petersen vertex-zero cofactor into standard nine-input deletion with no size increase. Hash 98029eebd0d1a2da625f275ad4d9944dc3aed3dcef6c33620c6f71dae79a9abb. Assembly with MonoFirstChecked for unconditional monotone two-drop and conditional floor18 in progress.

## Finite AO Petersen route (2026-11-25 15:17 UTC)

Launched three600-second19-gate AO2 searches after root15:12:27 renewal: firstAND(0,1), firstOR(0,1), firstOR(0,2). In a least circuit, firstAND(nonedge) is false on every prime pair and can be deleted; the old fifth symmetry case wasNOT and is absent here. Encoder uses30 exact monotone boundary rows, ordered active inputs, leadingOR(0,0) padding, all active gates used, row incomparability, both boundary clamp bounds, lex order, and pair symmetry. No solver verdict yet.20-gate pinned positive control passes and was independently checked on1024assignments, all15READ1pairs, allCNFclauses. Complete artifacts in `results/orch2590/sat`. Checked boundary and ordered-pair orbit certificates in `lemmas/sat_strategy`; v2 boundary adds pairwise accepted unions for the15 negative masks, supporting root CNF route.

[2026-11-25 15:17:44 UTC, proof_strategy] MonotoneTwoDropChecked.lean compiled exit0, hash abb0579b1fc8d9ecdf57a870870f037e19448fde12ee2bc443e7649c5445b973. Final petersen_two_drop_mono unconditionally gives some zero-vertex cofactor computed by Monotone2 D with D.size+2≤C.size. petersen_floor_of_nine_floor transfers any standard nine-vertex monotone lower bound k to full Petersen k+2. Full L8035 integration prepared separately but not yet compiled.

CHECKED read1subclass at 2026-11-25T15:20:34.598627+00:00: results/orch2590/lemmas/counterexample/PetersenReadOne.lean (Defs-only inline genericL4897.General and finitePetersen specialization). IsAO2+exactPetersen+IsReadK1 implies20≤size. Fullcompile exit0, warningsonly. This is apartial because arbitrarymonotone→read1 unproved.

Timestamp 2026-11-25T15:22:17.854172+00:00

## Toolchain agent: pin budget and three-neighbor signal

`lemmas/toolchain_setup/PinBudget.v3.checked.lean` (SHA256 2df8a9802f5ea7d42eadf0f9bd294e2d7039bc07c0ceb030ada84862a426b4d9) passed pinned Lean, exit0, one push_neg deprecation warning. Matching immutable logs and manifest are adjacent. A live 19-gate Monotone2 circuit with every primary appearing at least twice has every primary appearing exactly twice and each nonoutput internal wire appearing exactly once. With essential-primary usage at least once, the explicit dichotomy is singly-read primary OR this formula shape. Minimality-to-liveness bridge is proof_strategy's task.

`ThreeNeighbors.v1.checked.lean` (SHA256 36abeb61a5938098c1256487573e3ef6efeabb51f5f8126be9877d254a99b573) passed pinned Lean, exit0, empty logs. A Boolean signal false at zero and true at at least three singleton assignments cannot depend on only two coordinates. This supports a unique-reader AND context restriction, pending reduction_strategy's controlling-signal bridge.

Cofactor floor16 is sharp (L8035 lower bound, L1001 explicit16 witness per proof_strategy). Any floor20 proof via the zero cofactor needs four removed gates or structural information about the remaining16-gate circuit. Formula-only idea, not yet proved in Lean: a variable occurring once forces an AND sibling accepting its three neighbor singletons (at least two gates), plus an OR ancestor to retain edges not incident to that variable; restriction to zero can prune at least four gates when there is no sharing. This does not settle the all-variables-twice formula branch or the singly-read-input DAG branch.

Research read2026-11-25: https://www.imsc.res.in/~karteek/thesis (Sreenivasaiah,2010), girth-at-least-five formula lower bound is only |E|/2 leaves, insufficient here. No sourced theorem excluding read-twice Petersen formulas was found. The possible general claim C3/C4-free minimum-degree-three graph functions are not read-twice remains UNVERIFIED, and no proof relies on it.

[2026-11-25 15:23:18 UTC, proof_strategy] LeastLivenessChecked.lean fullcompile exit0 hash d7c6207996511a3b49198a9d5a59ade97cac0ed5a1b5acf2c5186af0e45f24b7. New drop_alias_mono/drop_dead_mono retain MonoL; least_mono_gate_read proves all nonoutput gates read; petersen_input_used gives≥1 occurrence for each primary input; least_mono_gate_used expresses gate liveness using PinBudget.pins counts. Ready to combine v4≤19 budget dichotomy.

Counterexample agent froze afterrootleasefailure at 2026-11-25T15:24:28.281386+00:00. BaseReadOnefloor20 CHECKED andpreserved. Edgewiseunread-edgecorollary pending, notclaimedchecked. Currentcompletecompilerlogsandsolverlogscopied toartifactdirectory. Two newmonotone localSATwindows UNKNOWN at60s each. Coverprofiles purelyfinitecombinatorics saved.

## SAT route frozen after lease loss (2026-11-25 15:24 UTC)

All three initial AO19 branches finished UNKNOWN at600.00 wall seconds: ANDedge217.05CPU/45.25MB, ORedge220.75CPU/38.16MB, ORnonedge228.48CPU/42.37MB. No candidate or UNSAT certificate. Prepared but NEVER LAUNCHED: formula-read2, general nonREAD1, formula nonREAD1 variants. Clean monomial encoding uses OR-reachable singleton proof flags; AND annihilates linear flags and creates quadratic flags from cross-products. It does NOT substitute ordinary singleton evaluations. Missing READ1 is existential across all15edges, compatible with full first-pair symmetry. Positive control matching7 was SAT and independently verified on16rows withboth primeedges lacking READ1; negative control Petersen20 stars was correctly UNSAT when unread-edge was required. All full outputs/data/CNFs saved under `results/orch2590/sat`. No active SAT or Lean process remains. Checked boundaryv2 and pair-orbit certificates remain frozen.
Statuscorrection: edgewisecorollary compilehadalreadyfinishedbeforefreeze; collectedexit0at 2026-11-25T15:24:39.223139+00:00. PetersenReadOneEdges.lean isCHECKED, including∀size≤19AO2correctC,∃orderedPetersenedge withreadsAtMost1=false. No buildwasresumed.

## Lease loss and unlaunched strongest searches

Third lease invalidated prematurely, latest successful renewal15:20:28 advertised15:40:28. A manual15:23:45 renewal failed. All agents stopped. The pending full18 certificate has not finished. The exact read1 lower20 and existence of an unread1 edge in any19candidate are checked. NewSAT variants require an existential bad edge (preserves first-pair symmetry); proof-monomial linear flags propagate only through OR, never use ordinary singleton evaluation. Matching2 graph7gateCNF is validated nonread1 positivecontrol; Petersen20star is rejected as expected. Strong variants and formula-only variant were prepared but never launched. Reader-budget stronger restrictions also remain partly unchecked.
