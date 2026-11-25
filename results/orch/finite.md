# Finite lower bound strategy — L-meta-2592

The two candidate sources are `L_meta_524.lean` and `L_meta_8367.lean`.

`L_meta_524` implements live-wire signature enumeration with a remaining NOT budget. Every state contains the signatures of still-live wires on a chosen list of positive/negative row pairs. A state is rejected if it has more live wires than the remaining binary-gate budget plus one, or its wires fail to distinguish some positive/negative pair. Each transition computes AND, OR or NOT, chooses whether to keep its operands alive, and rejects constant/duplicate results. Kernel certificates split this search across many concrete states.

`L_meta_8367` is substantially stronger: it normalizes arbitrary negations into signed two-input gates, makes NOT free, uses live-wire states, lower bounds on restrictions and graphs of certificates. It proves that Petersen minus one vertex needs at least 16 actual gates, by combining the monotone 16-binary bound and a signed 15-binary bound. The file already occupies 524,213 bytes; stripping blank lines, comments and leading whitespace saves some room, but building a new10-input certificate remains a substantial separate computation.

A useful new pruning consequence: a hypothetical19-gate Petersen circuit can lose at most3 gates when any single input is fixed to0, because each of its vertex-deletion restrictions needs16 gates. Any structural argument forcing a4-gate elimination would close the target.

A scratch live-wire search is at `/tmp/oec/pequalnp-pilot-108/finite_search.py`. It selects all400 adjacent positive/negative hypercube pairs of the Petersen edge function, uses directional separation after the final NOT, memoizes at most100,000 rejected states, and obeys a wall-time limit. This is an exploratory implementation, not a Lean certificate or a complete unsatisfiability result.

## First bounded experiment

A40-second run at budget19/exact remaining NOT budget1 visited51,200 states (22,842 memoized rejections), reached depth11, and timed out inside the initial NOT-on-input branch. The400critical pairs cover340distinct truth-table rows. No unsatisfiability or witness claim follows from this timeout. The unoptimized Python search is a feasibility probe only.

The9input certificate file can shrink from524,213bytes to509,554bytes by stripping blank lines, line comments and leading whitespace; only14,734bytes remain below the512KiB cap for extensions. This is a size calculation, not a changed Lean file.

## Signed search with restriction bounds

At 2026-11-25T14:12:37.941941+00:00, launched a300-second probe of the first-AND-on-edge orbit with18binary gates and free negation. The four normalized operations are AND, OR, AND-NOT, and reverse AND-NOT. Every truth-table signal is represented exactly over1024assignments. There are65restriction domains:10single-zero,45double-zero and10single-one restrictions. Signed lower bounds for proper induced subgraphs come from the `Known true` chain through `known383` inL8367, transported by explicit graph-isomorphism checking; every9vertex deletion uses its checked signed bound15. For a single-one restriction the three neighbors become independent linear OR inputs, and the remaining six-vertex graph supplies the other lower bound.

Each restriction maintains a bank of all distinct nonconstant restricted prefix signals, a paid-gate count, and the number of current live wires that become constant. The pruning inequality is `remaining + paid < lower + constant_count`, matchingL8367.projected_bound. A stored rejection of a live state is intrinsic to that state: the prefix supplies an explicit low-cost construction of its restricted wires, so it is safe to reuse the rejection at the same remaining budget. The Python program is exploratory; extracting a Lean certificate and checking every imported lower bound remains necessary.

## Stronger partial obtained from the signed bound

The checked signed9vertex certificate excludes14binary gates even when negation is free. Fixing one essential input of the fullPetersen function to0 must remove at least one binary gate. Therefore the full function needs at least16binary gates, strengthening the existing15+NOT-count bound and excluding all19gate candidates with4or moreNOTs. Root assigned status_and_review to the cost-preserving circuit restriction bridge. I extracted a dependency closure of the9vertex signed certificate to `results/orch/lemmas/SignedFloor.lean` and added `signed_binary_lower`. Initialextraction:755declarations,4127lines,245230bytes; provenancecomments addedafterward. Leancheck runningwith only `PEqualNP.Defs`.

The first300second signed18binaryAND-edge-orbit probe timedoutafter1,858,560states, with1,120,014restrictioncuts,726,081coveragecuts and7,301memoized rejectedstates. It reacheddepth12. No completeorbit certificate was obtained. The restriction implementation was separately tested against anexplicit20gate monotone circuit onall1024assignments: everyprefix satisfies everyrestrictionbound, withminimumslack1. This is a sanitycheck, not a proof ofthe pruningtheorems.

## Checked extraction bridge

`FullRun.lean` compiled successfully using the temporarylocalmodule `SignedCore`. It proves `circuit_run`: everyfullPetersen circuit satisfyingFanInTwo yields a generic free-negation `Run` fromthe10inputprojections, withnumberofbinary steps atmostitsnon-NOTgatecount. Theproofusesexact1024-bit truth tables and theoriginalL8367 extraction lemmasadapted to10inputs. Itdoesnotclaimthetarget lowerbound. Its535-line source is~27KB. `ReachRestriction.lean` also compiled, provingthatReachandAvailable transportalong arowmap. Buildlogs arepreserved inresults/orch/finite. Temporarymoduleimportswillbeeliminatedbyconcatenatingthecheckedhelpersforanyfinalsingle-file submission.

The signed17two-minuteprobe endedwithoutcertificate:640512states,414022restrictioncuts,222282coveragecuts,2585memoizedrejections,maximumdepth12. The counterexampleagent has takenover a30-minute continuation forfirstOR/nonedge.
