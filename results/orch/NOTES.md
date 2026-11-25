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
