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
