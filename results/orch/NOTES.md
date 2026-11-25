# L-meta-2592 orchestration

Desk assigned Petersen edge-function lower bound for <=19 fan-in-two gates with at least one NOT. Only PEqualNP.Defs project import allowed. Exact data: /tmp/oec/pequalnp-pilot-121/desk-001.json. Three live reductions already reported, so prioritize full proof/counterexample. Root alone owns desk and git delivery.

Strategies: proof_route = existing bounds/decomposition; circuit_search = finite synthesis; not_elimination = structural argument; status_review = independent audit. Use separate strategy notes and lemmas, notify root of results.

## Verified current reduction status

Public desk data saved /tmp/oec/pequalnp-pilot-121/gaps.json. All three easy reduction halves already checked: L-meta-4725 (15+NOT lower bound), L-meta-7389 (canonical normalization), L-meta-8295 (cut after last NOT). Remaining open child statements: L-meta-4727 (1..4 NOT), L-meta-7391 (canonical19), L-meta-8297 (last-NOT separator). Reproducing existing easy halves is useful infrastructure but not new proof progress. Aim for stronger gate deletion or explicit witness.

## First strategy review

The seven-row block-cover conjecture requiring ps.length+bs.length >=12 is false: a budget11 auxiliary construction exists. This is not a counterexample to L-meta-2592. Stronger samples are needed for the ledger route. The direct eight-profile lower bound is a different statement and cannot simply replace the ledger condition. A monolithic finite kernel check exceeded memory; smaller certificate chunks are being prepared. The one-NOT decomposition and Petersen generator lemmas are compiled and their actual-circuit link is in progress. Witness searches remain inconclusive.

## Stronger counting route

Adding the independent core pair (0,1) to zero and six singleton rows gives eight regular rows. A complete auxiliary block-cover search found no budget11 construction, independently rerun with matching state counts. gate_elimination ports the finite CoverCheck proof; not_elimination ports terminal-class graph reasoning; toolchain_setup ports Probes and fixtures. Expected result, if linked: at least16 non-NOT gates for Petersen, excluding the four-NOT case. One/two/three-NOT cases remain.

## ProbesTen adaptation checked

2026-11-25T14:41:26.189111+00:00: ProbesTen.lean compiled against existing partial root module. Actual Petersen circuit-to-ledger link verified for eight regular samples plus two special rows and all five terminal layouts. no_ledger at nonNotCount<=15 reduces exactly to CoverCheckEight no_cover_build budget11. See strategy-probes.md for merge instructions and fixtures.

## Active step changed after lease loss

The retry requesting2592 returned L-meta-2583 instead. Active exact assignment is /tmp/oec/pequalnp-pilot-121/desk-002.json; statement is /tmp/oec/pequalnp-pilot-121/statement-2583.txt. All2592 work is paused and preserved. New focus: no-larger read-1 monotone circuit for projective-plane incidence. Reductions are closed. Roles: review=definition audit; gate=lower bounds; toolchain=explicit construction; proof_route=normal form; not_elimination=library/decomposition; circuit_search=small counterexamples.

## L-meta-2583 exact star construction checked

2026-11-25T14:51:48.595420+00:00: PlaneStarExact2583.lean compiles (664 lines) and gives correct read-1 circuit of exact size N(q+2)−1. normalize_from_bound finishes the target from N(q+2)≤C.size+1. Existing sharp lower bounds require read-1 and cannot be used circularly. Full details in strategy-2583-construct.md.

## L-meta-2590 current assignment

2026-11-25T15:20:25.601367+00:00 Valid desk assignment followed by successful renewals; prove unrestricted monotone Petersen circuit size at least20. Exactstatement: /tmp/oec/pequalnp-pilot-121/statement-2590.txt. Reductions are enabled but allthree slots are occupied.

ReadOnePetersen2590 is compiled, independently reviewed and pushed at816be3f7; its IsAO2 and jointread1 hypotheses remain essential. SAT and stochastic searches use all15 minimaltrue edge rows and15 maximalfalse independentset rows;20gatecontrols passall1024assignments. Generic Heawood surplus-flow helpers may transfer; no unrestricted Petersen20 theorem found in bounded repository census. Two priorleases returned410 before statedexpiry; no reason established and no releasecalls made.

## L-meta-2056 current assignment

2026-11-25T15:40:49.261378+00:00 Need63gate monotone Singer13 circuit for exactposted sumincidence relation. Positive52edges and704negative maximalindependentsets; postedsubset≤3 testscoverallmaximalfalse rows. Prior2583 work reused via line sign relabeling,64gatecontrolvalidated. Reductionsenabled but3slotsalreadyoccupied. Sixdifferent strategies running.

L-meta-2056 checkpoint clarification: no complete proof, refutation, or accepted local checker verdict exists. PackedChunks2056 is a compiled verifier plus a64-gate positive control; the posted budget is63. A core witness does not automatically extend by one gate per private leaf: such deletions justify lower bounds, while constructive extension requires actual factor positions. Star-extension infrastructure applies to full point patches.


## L-meta-2056 shared checkpoint at18:31 (superseded below)

As of 2026-11-25T18:31:24.386520+00:00, no complete target proof, refutation, accepted target checker verdict, or PR exists. The named file is still the 728-line partial verifier and 64-gate control. See CHECKPOINT-2056.md and validation.txt for the compiled components and full log locations.

Compiled and independently reviewed necessary conditions now include at least ten actual AND gates for a correct full-plane circuit, and at least64 total gates under explicit IsAO2/full correctness/IsReadK1 hypotheses. The latter now uses the exact Nat-sum incidence relation directly, via negation matching; it is preserved at commit2dcffd2e6f9e339e9ca81f51d7f4cac22dad3b11. Neither condition proves the unrestricted target.

Current native runs, all frozen for their original3600-second configurations:

- circuit_search: global at-most12-AND/free-OR query, native start18:05:41.211 UTC; nominal cap19:05:41. A SAT model needs ordinary gate-count postprocessing and verification. Source d8acbf7a; disjoint operands are justified only in this free-OR setting.
- toolchain_setup: component grammar V3, start18:06:47.275; cap19:06:47. Strict ranks prevent cyclic realizations. A SAT model directly has at most63 selected noninput profiles and is decoded/replayed. The finite grammar is restricted.
- gate_elimination: full63/756-row first-gate query, start18:09:32.155; cap19:09:32. Source b9b6a04c; complete normalizations and symmetry controls independently reviewed.
- not_elimination: K16 bounded-membership nested query, start18:12:24.026; cap19:12:24. Source0b7a5652; its cost upper bound guarantees at most63 ordinary gates for any decoded model. This is a restricted construction model.

A transient Git authentication failure interrupted publication of the new Read1 helper. The shared safe-read retry ladder recovered, confirmed the old remote SHA, then a same-credential expected-SHA-fenced push succeeded once. No credential or remote changed. All four native processes were SIGSTOP-paused for48–75seconds and SIGCONT-resumed without restarts or query changes. Original timeout configurations remain; complete records are in auth-recovery-037 and each owner's pause/resume metadata.

Reviewed successor work is separate from the running sources: the full SAT non-read1-edge exclusion, larger component grammar V5 with output reachability, positive-profile normalization for the bounded model, and shared-OR/directed-cleanup postprocessors for free-OR models. Additional warm phases and conjunctions of normalizations must finish independent controls before launch.

Important correction: a two-input first-AND edge anchor is sound for the free-OR model after disjoint normalization; it was withdrawn for the bounded-membership model because shared primary sources can make accepted edges fail to split across the two operands. No running source contained that invalid inference. A separate weaker single-input anchor subsequently passed independent source and native-control review.

Final-round planning: when the current runs finish, use at most one stronger stable successor per slot, normally2400seconds, with an absolute search stop around20:00 UTC. Reserve the remaining time for any witness integration, exact Lean build/checker, capped cleanup, independent review, publication and own-lease release. If no witness appears, preserve all reviewed work and report the unproved target honestly. Do not restart active queries merely to add another minor constraint.


## L-meta-2056 re-plan after existing thirteen-AND theorem

As of 2026-11-25T18:48:29.106960+00:00, existing L_meta_1898.lean (source SHA256 d44d58c30bc802ab764e63cac4a19218e353c38f91dc036a767367ea9ac60762, final theorem lines7314–7334) has been independently inspected by four agents. It proves at least13 actual ordinary AND gates for any Monotone2 circuit satisfying all difference-incidence positives and a subfamily of genuine independent negative assignments. There is no size, ReadK, or normal-form assumption. Full correctness supplies those tests; negating line input indices transports sum incidence and preserves every gate operation. A local rebuild of this existing theorem is pending. Earlier statements that no applicable13-AND theorem was found were incomplete search reports, now corrected.

The global at-most12-AND/free-OR query and all its planned successors are therefore known impossible under this existing theorem. The native worker was stopped and reaped at18:47:35.453429 UTC: wrapper143/native−15, no SAT/UNSAT verdict. Complete diagnostics and termination metadata are preserved; this is not a solver UNSAT certificate. The remaining full63, boundedK16, and finite-component queries continue unchanged. A boundedK13 successor is being prepared, subject to controls.

The exact sum-incidence read-one lower bound remains conditional on IsReadK1. A cheap compressed-model non-read-one constraint is under independent mathematical review. No unrestricted64 lower bound or63 construction has been established. A narrowly scoped OR-count theorem census has not found an unrestricted51 lower bound.

The latest upstream read is6050bcb669b3391d673876601ea117e3d59075f3. A complete final-statement census of358 newer Outside files and a bounded helper census found no applicable q3 construction or generic shortcut. Upstream repository API resolves the historical brilliant-hq alias to open-goat/pequalnp-proofs, same repository ID1468025030. Complete paginated open-PR searches found zero2056, zero3773, and one650 reduction PR16265; no construction is claimed from these search results. The checker change only classifies OS OOM failures; positive verification logic is unchanged.
