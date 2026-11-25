# Independent review: normalized K4 quiet obstruction

Verdict: PASS. Build completed exit0 with the reviewed source hash; complete diagnostics contain only deprecated if_false/if_true warnings.
Frozen file: formalization-k4-single-reader-refutation.lean
SHA256: 05fed5d00b2bdb1e6ac3a6e6f3a627ff41e7c4ee36a38dd820ff26ade5ea6098
Lines: 5,324.

The frozen5,171-line K4 equality source is preserved exactly except its final namespaceclosing was moved. The independentlyreviewed generic single-reader trace bridge is copied exactly. I independently read that bridge and the newgraphcorollary, then checked bothfinaltheorems.

SingleReaderTrace states exactly the raw binary Booleanproductrule andOR recurrence, with a one-hot inputderivative seed. The graphcorollary obtains false at singleton u from looplessness andtrue after inserting v from the edge(v,u). The equalitytheorem gives the required single-reader chain whenv is an originalK4vertex. Every K4edge has one originalendpoint, so choosingitsderivative gives true andcontradicts twofalseoutputderivatives. Orientation of td/te is correct inbothbranches.

The claim is restricted to strictlive10-inputDAGs, last-wireoutput, exactK4semantics, and≤15gates. It is not the fullFano27refutation, and doesnotclaim preservationthrough arbitraryCircuitnormalization or eliminationof fourunusedinputs. No forbidden_root_,stringliteral,sorry,native_decide,ornewaxiom found.
