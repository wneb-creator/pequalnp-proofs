# L-meta-2590 Petersen counterexample strategy

Extracted the exact fifteen-edge Petersen graph and independently enumerated its fifteen maximal false assignments, matching R_meta_2590_1. Built a twenty-gate monotone binary circuit from the six-vertex cover complementary to independent set 116. Exhaustive evaluation on all 1024 assignments passes. This validation is Python only so far.

Data: /tmp/oec/pequalnp-pilot-144/counterexample2590/petersen_cases.json. Gate representation is [operation, earlier wire, earlier wire], operation 1=OR and 0=AND, inputs0..9, output29.

## Checked partial
PetersenSamples.lean passed Lean 4.36.0 via lake env lean -M4096 (exit0, empty samples-build-1.log). It verifies size20, Monotone2, circuit evaluation on all30 decisive rows, and target values on those rows. Full-function equality is currently being checked separately.

## Model caveat
Monotone2 allows constant/unary gates and forward/missing wire reads, unlike IsAO2. Constant propagation and wire renaming can normalize these for a nonconstant target without increasing gate count, but any strict-AO2 SAT lower bound needs that argument formalized. No model exploit found.

## Full upper-bound partial checked
PetersenSymbolic.lean compiled successfully (exit0; symbolic-build-5.log). It verifies the twenty-gate circuit computes the posted Petersen function on every Fin10-to-Bool input. The proof uses symbolic circuit simplification, Boolean distributivity, and ac_rfl. The sole warning is a redundant simp argument; a cleaned version PetersenUpper.lean is being checked. This establishes an upper bound only and does not prove the posted impossibility for nineteen gates.

## Heuristic near witness
The current best nineteen-gate circuit omits edge(4,9). Exhaustive validation on1024inputs finds zero false positives and nine false negatives. It is not a counterexample; all data and diagnostics are in counterexample2590/.

## Final heuristic run
Ran600seconds with84,130,827mutations and1683restarts; minimum error remainedone ofthethirtydecisiverows. No validnineteen-gate counterexamplefound. Searchterminatedatitsrequestedbound.

## Generic model normalization checked
Normalization.lean compiledclean(exit0, normalization-build-3.log). ItstrengthenscheckedL_meta_1527constantpropagationwithduplicate-operand elimination: anynonconstantMonotone2circuitadmitsano-largerAO2circuitwithNodupinputsandsamefunction.

NormalizedLive.lean compiledclean(exit0, normalized-live-build-2.log). ItaddsgloballyleastMonotone2representativechoice, thennormalization,andunusedgatedeletion (helpersadaptedfromLift,LiftFix,andNormalForm). Itsnormalized_live theoremreturns: no-largerAO2D,Nodupgateinputs,outputn+o foro:FinD.size,andpositivefanoutforeverynonoutputgate. Assumptions:0<n,nonconstanttargetf,andfnotanyinputprojection. ThisclosesmodelnormalizationforPetersenoncesmalltargetfactsaresupplied.

Finalclean20gateupper-boundsource:PetersenUpper.lean(exit0, upper-build-1.logempty).
