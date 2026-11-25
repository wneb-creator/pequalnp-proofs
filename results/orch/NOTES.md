Shared research notes for L-meta-2592

Only the root holds the lease and submits. Exact statement: /tmp/oec/pequalnp-pilot-113/desk-next-001.json. Three reductions already live; seek full proof or counterexample.


Counterexample route: checked exact Circuit/FanInTwo semantics; invalid reads give false and NOT counts as a gate. No loophole found. No z3/pysat/SAT binary installed; attempting C++ full-truth-table stochastic synthesis. L_meta_6194 supplied by library agent gives at least 15 non-NOT gates, hence only 1..4 NOT gates need consideration.

2026-11-25T14:15:42.648077+00:00
## Library route findings

- L_meta_4725.lean (3224 lines) proves exactly Petersen `15 + NotBracket.notCount C ≤ C.size` under FanInTwo and computing the target. Its full helpers are self-contained under Mathlib + PEqualNP.Defs. L_meta_6194.lean (3255 lines) proves the equivalent non-NOT gate floor 15.
- Therefore any circuit refuting L-meta-2592 has 1–4 NOT gates.
- L_meta_7389.lean (305 lines) proves exactly the normalization premise of R_meta_2592_408: normalize forward/default reads and extra NOT operands, trim output, preserve a NOT or strictly reduce size.
- Existing reductions R_meta_2592_271 (binary floor plus few-NOT bound), _318 (last-NOT cut plus monotone-suffix separator), and _408 (normalization plus legal-circuit lower bound) account for all three slots.
- L_meta_8021.lean is vacuous: it assumes no NOT gates and notCount at least one simultaneously; it provides no useful few-NOT result.
- Checked ten-input circuit theorem census: 75 statements; no direct full Petersen 20-gate lower bound found. Most substantial nearby progress concerns the nine-input Petersen-minus-vertex cofactor. L_meta_8033 proves size≥15 and 13+notCount≤size there.
- Model semantics contain no obvious shortcut: out-of-range/future reads are false, NOT ignores operands after the first, empty NOT=true, gate count is list length.

2026-11-25T14:19:16.548241+00:00
Formal invariants route: drafted explicit Petersen automorphism certificate (100 ordered-pair witnesses selected from 120 verified S5-induced permutations), graphFn invariance, exact target-expression bridge, and generic circuit input-renaming equivariance with size/fanin/NOT preservation. Files under /tmp/oec/pequalnp-pilot-113/formal-invariants/{Automorphisms,Rename}.lean. Independent reviewer checked permutation table mathematically; Lean compilation awaits Mathlib cache. OutputBounds.lean draft is redundant with checked L_meta_7389 and should not be shipped.

2026-11-25T14:19:26.731900+00:00
## Lower-bound route and last-NOT helper

- Draft helper file `/tmp/oec/pequalnp-pilot-113/LastNot.lean` proves the first premise of R_meta_2592_318: split any FanInTwo circuit at its last NOT into prefix P and monotone suffix Q, preserving total size and evaluation. Empty-input NOT uses a provably missing output wire of P. Independent mathematical review found no error; compilation pending project Defs build.
- Source read 2026-11-25: https://pequalnp.com/papers/note-1 gives graph lower bounds only on forests, cycles, and spaced hubs. Petersen lies outside those classes. Generic reader elimination (3 gates at input0 or4 at input1) is insufficient alone: false cofactor lower16 gives19, true cofactor is3 free OR inputs plus C6 and lower11.
- A NOT on input p can in the tight pattern lose only3 gates at p0: the NOT, one positive OR reader of p, one AND reader of its negation. Deriving4 needs a new equality-case monotonicity argument. An internal first NOT of an OR need not become constant after a single input0 restriction. No universal4-saving theorem established.
- Possible equality-case target: reinserting a degree3 vertex needs4 gates unless a minimal16-gate cofactor circuit can reuse an OR of two of its independent neighbors. Ruling out that reuse may bridge16+4=20, but remains unproved.

2026-11-25T14:20:48.365120+00:00 Library route update:
- Found the full cofactor16 theorem L_meta_4033: ¬HasCircuitSize9 Petersen-minus-vertex15, 6579 lines/521569bytes. Its signedRoot also proves any free-complement signed binary circuit needs at least15 non-NOT gates.
- Better reusable baseline is L_meta_6581: 4555lines/284540bytes, imports Mathlib+Defs. Already includes signed cofactor15 certificate (nineFloor4496) and full Petersen >=16 non-NOT gates (atLeastSixteen4505). Projection sets one raw variable0 and charges one constant livewire via projected_bound583. It is substantially smaller than4033 because mono certificates are omitted.
- Potential strengthening: first binary gate inputs must both remain live for Petersen (otherwise fixing one input to a controlling value loses dependence on the other, violating an edge witness). For AND restriction of one input to0 leaves rawzero + outputzero: two constant livewires after one consumedgate, giving >=18 binaries from cofactor15. OR gives rawzero + duplicate(otherinput, ORoutput); needs duplicate-contraction analogue. This may exclude 2+NOT gates at19total, but exactly1NOT remains.
- Sent explicit20gate seeds L_meta_584 and L_meta_587 to counterexample agent.

Counterexample search update: CaDiCaL source cloned from github.com/arminbiere/cadical and built in scratch. Incremental CEGIS searches on19gates started for first AND(edge) and first NOT(input),20minute limits each. Initial41 rows are empty input,10singletons,15edge minterms,and15maximal independent sets; each SAT model is tested on all1024 rows before acceptance. Encoding has normalization/symmetry restrictions; UNSAT would be restricted search evidence until formally justified. No witness yet. Stochastic search has found only approximate circuits; best enforced-NOT candidate so far has15false negatives and a deadNOT, so it is not a result. A newer variant requires reachableNOTs and capsNOTs3, using checked16non-NOT floor reported by library agent.

Counterexample search, first completed stochastic run: 1,605,580,001 candidate evaluations in 600 seconds; no exact circuit. Best had 9 false negatives and no NOT (weighted score10 included a no-NOT penalty). This is non-exhaustive search, not a lower-bound proof. A second run retains NOT gates; a third now requires a reachable NOT, allows at most3NOTs, and adds the checked nonlinear L_meta_58420-gate seed. Independent rules_review validated the CaDiCaL encoding positively against the checked L_meta_58720-gate circuit on all1024 inputs. Berkeley ABC was cloned from github.com and is building for a separate technology-mapping search in the AND2/OR2/NOT basis.

2026-11-25 14:25 UTC correction: LastNot decomposition already exists as checked L_meta_8295 (66 lines). Our independently derived helper is sound but redundant. Remaining open direct children are L-meta-4727, L-meta-7391, L-meta-8297.

2026-11-25T14:26:09.909869+00:00
Correction: public catalogue search by root found L_meta_8295 already proves the exact last-NOT cut (66 lines). Our independently compiled LastNot helper is sound but redundant; it does not close a new subproblem. Current effort is the stronger first-AND signed-binary lower bound18.

2026-11-25T14:27:04.616786+00:00
Formal invariant result: Rename.lean compiled with exit 0 and empty log; independent rules_review audit passed (SHA256 6a334e82fe4d654a7d63aa6dc78f4bcfc28a6c2abe748f3e95b62a485ec4bf66). Input renaming preserves arbitrary gate semantics, total size, fan-in-two, and presence of NOT. Automorphism certificate switched from elaborator decide to ordinary kernel decide for resource use; canonical first-gate lemmas drafted for the five symmetry cases, conditional on nontrivial raw-input first gates.

2026-11-25T14:29:45.685134+00:00
Automorphisms.lean compiled with exit0, empty log; independent final audit PASS (SHA256 412af479a2ae6a0f98cbfd8c0067db026dfc2bd9af92ec4ce75ae28aadf95cab). All100 ordered-pair maps are bijections preserving100 adjacency pairs. Exact Boolean graph target bridge proved. Pair/vertex transitivity now Lean-checked; final combined canonical-first-gate statements are compiling. Ten p_i maps with p_i(i)=0 exported to formal-invariants/vertex-auts.json for lower_bound cofactor embeddings.

Search resource adjustment: container quota is4CPUs, so extra stochastic processes and the4-worker ABC build were stopped, preserving full logs and best candidates. At most2SAT plus1stochastic process remain. The unweighted12-error approximation had2cancelling NOTs and is not evidence of a negation advantage; the next stochastic variant excludes doubleNOT, constantNOT and copy-gate patterns. A local SAT repair implementation is ready, allowing≤3gate-description changes around a candidate and checking all1024rows. No exact witness.

2026-11-25T14:35:48.780558+00:00 orchestrator replan: target unconditional17 non-NOT gates as next substantive component. First-AND/signed-AND constant projection aims18binary; first-OR aims17binary. A generic duplicate charge is false and was abandoned. Exact19gate SAT and local repair remain counterexample routes. Hardware4CPU/16GiB; serialize heavy Lean certificates. Upstream refresh showed102 changed Outside files and no newer direct17binary theorem.

2026-11-25T14:38:04.651817+00:00
Canonical.lean final narrowed-import build PASSED, exit0 and empty log; 334 lines, object file generated. Proves size/fanin/NOT-preserving canonicalization of a first binary raw-input pair to adjacent(0,1)/nonadjacent(0,2), and first raw-input NOT to input0. This is conditional on the stated first-gate shape, not a proof that all minimal circuits have such a first gate. Next helper DropCopy deletes unary/repeated-input first AND/OR gates, preserving NOT and saving one gate; drafted and undergoing a light structural proof check.

## Library route: checked first-gate components

FirstOr.lean, FirstAnd.lean, and FirstStep.lean now all compile against the actual checked L_meta_6581 olean (logs under /tmp/oec/pequalnp-pilot-113/library-route). First OR on pin0 and any other raw pin forces at least17 non-NOT gates; first AND or signed AND forces18. FirstStep extracts an arbitrary distinct raw pair and signed operation from any nontrivial normalized Live proof. GlobalData and GlobalWitness are being checked by lower_bound; GlobalOr, GlobalAnd, GlobalCount drafts combine these into unconditional17 non-NOT and exclusion of three or more NOT gates in size19. The full requested one-NOT/two-NOT cases remain open.

Do not claim an extra charge for duplicate projected wires: that suggested invariant was rejected by a concrete majority-of-three counterexample. Valid charges count projected constant wires only.

2026-11-25T14:39:24.099867+00:00
## New checked first-AND partial

- FirstAnd.lean now compiles against genuine L_meta_6581. For a live signed-circuit derivation whose first binary operation is AND(pin0,pinj) or AND(pin0,NOT pinj), with j nonzero and all other live wires raw inputs, the derivation needs at least18 binary operations. This is a conditional frontier statement, not the full posted gap.
- Explicit two-row witnesses force pin0 to remain live after the operation. Restricting pin0=0 makes both that retained input and the computed AND constant. The checked nine-input lower bound15 plus two constant charges gives tail17 and total18. Independent mathematical/format audit passed.
- Generic OR gives total17. Draft GlobalData maps each vertex-deleted cofactor to the checked nine-input graph; GlobalWitness forces retention for all270 ordered raw-pair/operator cases. Their finite checks are serialized to fit memory.
- Avoid decidable `forall a in initial` over1024-bit words: it can select full BitVec enumeration. Use initial.all explicitly.

2026-11-25T14:41:58.772622+00:00
DropFirst.lean (236 lines) checked with exit0 and empty log. It includes first-copy deletion (AND/OR with [a] or[a,a], valid raw a) and first-constant-false deletion (including OR[]). Both save exactly1 gate while preserving all evaluations on length-n inputs, FanInTwo, and remaining NOT operations. False wire is redirected to n+tail.length, permanently missing in the shortened circuit. These normalize degenerate first gates in minimal NOT-containing counterexamples; they do not eliminate an essential NOT. Independent review pending.

2026-11-25T14:43:08.910808+00:00
## Globalization certificates checked

- GlobalData.lean passed actual Lean with saved GlobalData.olean. It certifies all ten cofactor embeddings, all5120 target row equalities, all51200 raw-input restrictions, chosen-pin-zero and input availability. Log global-data-actual-002.log is empty success.
- GlobalWitness.lean passed actual Lean with saved GlobalWitness.olean. Its270 ordered first-gate cases cover AND, OR, and signed AND; all use explicit List.all over ten raw pins. It proves first_pin_retained for arbitrary distinct input pair. Log global-witness-actual-001.log is empty success.
- GlobalAnd.lean generalizes the compiled first-AND18 bound using those certificates and explicit hNineFloor. library_route is checking the ordinary combined GlobalAnd/GlobalOr/GlobalCount proof for an unconditional17 non-NOT gate floor; that final combined result is not yet checked as of this note.

2026-11-25T14:43:35.756463+00:00
Independent global partial-proof review:

- Mathematical/source review PASS for GlobalData, GlobalWitness, FirstAnd, FirstOr, FirstStep, GlobalAnd, GlobalOr, and GlobalCount. Independent Python read their literal certificates and the actual L_meta_6581 tables: all1024 Petersen target rows, all5120 cofactor rows, all51200 pin restrictions, and all270 retention witness cases passed. Every embedAt maps bijectively onto the corresponding vertex-zero cofactor; all10 vertex maps preserve Petersen edges.
- Retention forces the first positive input to stay in the raw frontier. AND and signed-AND project both retained input and distinct gate output to constants, charging2; OR charges only the retained input, charging1. Signed operation3 equals operation2 with swapped arguments. FirstStep covers every normalized Live derivation via the upstream actual-circuit realization. No duplicate-wire charge or circular premise found.
- GlobalCount currently assumes exactly Lower true inputs graph15, independently proved by upstream nineFloor. Applying that theorem gives17 non-NOT gates, and the exact partition of all gates into NOT/non-NOT excludes at least3 NOT gates when total size is at most19. This does not settle the remaining one-NOT/two-NOT cases or L-meta-2592.
- Compilation status at review: GlobalData, GlobalWitness, FirstAnd, FirstOr, FirstStep reported actual Lean exit0 by authors, with all five corresponding logs independently confirmed empty. GlobalAnd/GlobalOr/GlobalCount combined ordinary build still pending; no independent compiler run was performed. Scratch imports of Outside proof/dependency modules must be replaced by allowed inlined helpers before any final submission, and the exact posted theorem/checker still must pass.

2026-11-25T14:48:04.920000+00:00
Independent final partial-source review update: PASS. CombinedOrdinary.lean, GlobalSeventeen.lean, and GenericBounds.lean now have author-reported Lean exit0; reviewed logs contain only if_pos deprecation warnings for combined/generic and no output for the unconditional wrapper. Reviewed final Finset/cost fixes preserve prior mathematics. GlobalSeventeen correctly applies actual nineFloor and establishes unconditional17 non-NOT gates and the three-or-more-NOT exclusion. GenericBounds consistently preserves arbitrary mode u and floor L: raw/constant pin availability works for both modes, OR gives L+2, (signed)AND gives L+3, and two_more gives global L+2. Its monotone_eighteen still requires the unprovided premise Lower false inputs graph16; no unconditional monotone18 claim is established here. No new concerns; exact gap remains open. No independent compilation performed.
CombinedOrdinary.lean SHA256 117ecf85745feef6db14499411ce78daed9759505c9c311a79ae0a446a56691b
GlobalSeventeen.lean SHA256 9d727a36b47d0b4a8373f933f75a90c59b9354eaf352047206858779177f3fa8
GenericBounds.lean SHA256 b0ac69dce45854aed67bce16297274b18301cf4ae4f6f4eaa0990ee58704efdb

## L-meta-2583 library census

Definitions: `ReadK.IsReadK n C 1` is joint proof-tree read multiplicity on every prime implicant, not input fanout and not the weaker single-read/double-reread notion. `TopForm.IsAO2` is exact binary AND/OR with backwards reads.

Checked exact read1 cost tools: L4897 extracts a bipartite vertex cover with |E|+|left cover|+|right cover| <= size+1 for C4-free graphs. L7684 constructs read1 AO2 from any bipartite cover at that bound. L7639 specializes the lower bound to a perfect matching, giving |E|+N <= size+1. These imply read1 lower bounds27 for Fano and64 for order3 planes.

Important: unrestricted monotone Fano >=27 is already checked in L971 (9367 lines). Thus a q2 counterexample cannot exist. For q3, the 135-file Fin26 census found only conditional >=64 lower bounds: L4803 no AND nesting; L5162 minimal with one ordered AND-ancestor pair; L1500/L2420/L5254 line-degree at most1. L1730 is a checked64gate witness. No unrestricted q3 >=64 theorem found.

Normalization support: L8385/L4181 produce no-larger least top-form circuits. L3653 and L3700 remove a single dirty AND under lift-fixed-point side conditions. L3652 places every doubly reread edge in a maximal core. Warning: L3444, L3446, L2969 refute natural core/cover budget inequalities even for bipartite C4-free graphs. L3679 refutes flat minimum-circuit normalization for general bipartite graphs using a Tarjan construction with many4cycles; it does not directly settle projective planes.

Complete statement indexes are in /tmp/oec/pequalnp-pilot-113/gap2583/{readk,topform,lift,plane,26input,42input,hoist}-statements.json. No existing theorem resolving2583 was found.

Final ownership correction: the desk returned leases whose terms.issue times predated this job. The L-meta-2583 retry returned the same existing lease and holding=5 note. Per the user instruction, all work stopped and no lease was released. The saved L-meta-2592 partials are compiled research, not a submitted solution. L-meta-2583 notes are informal and no new circuit-synthesis search or proof build was started.
