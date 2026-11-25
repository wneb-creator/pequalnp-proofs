# Same-side cooccurrence partitions

This separate extension retains the frozen AND incomparability encoder and adds 210 clauses with no new variables. For each of the 35 triples of point labels and 35 triples of line labels, the three clauses require transitivity of the existing primary-slot cooccurrence relation.

The mathematical reason is exact for a reconstructed p14 Fano circuit. Suppose distinct a,b,c lie on one side, a,b occur in slot S, and b,c occur in slot T. The accepted cover-free theorem, centered at b with nonadjacent a,c, gives a b-consumption slot omitting both. If S and T differed, this would be a third b-slot, contradicting the proved exact-two consumption count. Hence S=T, so a,c cooccur. The primary slot labels are exactly the consuming labels because every AND output has empty singleton support. No assertion that an arbitrary gate is a Fano biclique is used.

Target size is 32,615 variables and 137,621 clauses. The independently checked hosted matching control enables the partition clauses and all previous structural cuts; it is explicitly not a Fano witness. The exact 28-gate quiet Fano control disables the size-27 equality and partition clauses while enabling operand incomparability. The independent verifier checks the exact new clause blocks, primary-slot cooccurrence semantics, complete assignments, all 16,384 truth rows, both raw derivatives, and inactive suffixes.

No solver has run on this variant at preparation time. Restore the manifest files and run `python3 constructive-partition-audit.py ARTIFACT_DIRECTORY`. Executing the encoder also requires the frozen encoders in the preceding manifests.
