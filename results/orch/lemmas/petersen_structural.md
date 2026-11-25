# L-meta-2590 structural route

The new target rules out19-gate Monotone2 circuits for the Petersen edge function.

## Concrete route

For a live binary circuit of s gates, let R count input occurrences and U count internal-wire occurrences. R+U=2s. Each of the s-1 nonoutput gates is read at least once. If every one of10 inputs is read at least twice and s≤19, equality forces s=19, every input read exactlytwice, every internal nonoutput wire read exactlyonce, and output readzero. The circuit therefore unfolds into a20-leaf monotone formula.

Checked L_meta_531 gives |E|+vertex-cover≤formula leaves for trianglefree/C4free graphs. The lemma-search agent specialized this to Petersen: at least21leaves. Hence every normalized19-gate countercandidate has a singly-read input. This closes a genuine structural branch.

## Existing lower bounds and obstacles

L_meta_9781.Petersen.mono_floor proves a16-gate Monotone2 lower bound for Petersen minus one vertex (nine inputs, twelve edges). Thus false substitution in a19gate countercandidate may eliminate atmost3gates. No checked unrestricted≥18 lower bound for Petersen minus one edge was found. Hoisting a below-output edge conjunction does not automatically compute exactly the edge-deleted function, since larger monomials containing thatedge may remain.

## Checked partials

CountDichotomy.lean:39lines, first-attempt exit0, raw arithmetic counting theorem.
CircuitDichotomy.lean:count-fin, input-list length/range, and actual AO2 circuit balance compiled at iteration2. Extending with internal-use list nodup and the formula bridge.
Unfold.lean:260lines extracted/adapted from L_meta_2225.Unfold, compiled exit0. Produces equivalent positive DMFormula with leaves≤gates+1 when internal-use list is duplicatefree.

## OR-helper restrictions

Child dirty_blocks proved a singled-out-input OR helper can be true on an independent assignment avoidinginput0 only at two exceptional triples, {2,8,9} and {3,6,7}. The compiled component is structural2590/dirty-blocks.lean. These are the two bipartition classes of the six-cycle left outside the closed neighborhood of0. Additional deletion/symmetry facts are in progress.

## Completed structural bridge

SingleRead.lean (1098lines), logSingleRead2.log, exit0withno diagnostics: combines exactformula bound, circuit-to-formula unfolding, wirecounts, and essentialinputcount positivity. Mainhelper single_read_input proves anyliveAO2Petersencircuit of≤19gates withdistinctoperands andvalidgateoutput has aninputreadexactlyonce.

UniqueReader.lean (25lines), cleanexit0: a rawcount1 input determines a uniquegate in a before++gate::after decomposition, withthatinputabsentfromallothergates.

These close the all-inputs-readtwice branch. The remaining residualAND/OR bounds are not established.
