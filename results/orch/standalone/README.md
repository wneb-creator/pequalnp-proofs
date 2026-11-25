# Conditional partial, not a proof of L-meta-2448

The frozen source proves the posted star-profile existential under explicit extra assumptions on a supplied circuit: IsAO2, public minimality, correct graph function, and at most one junk AND gate. The unrestricted posted statement remains unproved.

The source imports only Mathlib and PEqualNP.Defs. Its build and final-helper axiom audit passed. Independent reviewers verified every retained declaration body, the documented namespace rewrite, scope, format, and standard axioms.

Provenance records refer to the source files at extraction time. The earlier named-file helper collection is preserved as ../lemmas/IntegratedRepairs.lean (2078 lines), and in branch history before the standalone replacement. The combined prototype is ../lemmas/AtMostOneJunkStarIntegrated2.lean. L_meta_3760.lean is the unchanged upstream source. Extraction scripts are preserved as provenance; their original absolute scratch paths describe this job environment.

The named gap file is now an exact copy of AtMostOneJunkStandalone.lean. The actual local checker must still reject it because the unconditional main theorem is absent. No proof PR should be opened for this partial.
