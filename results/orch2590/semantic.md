
2026-11-25T15:23:57.806379+00:00

## Checkpoint after lease disappearance

- SemanticRestriction.lean: kernel checked generic monotone constant/alias propagation, exact dropped-gate count, direct-reader and AND-consumer charging.
- SemanticChargeSet.lean: kernel checked finite charged union and full propagated drop-count <=3 under an explicit cofactor lower bound of16. SHA256 b83d6f1feb076eb6591660c1c4da05a9a97fa04a202361b481fc5597ade1b9eb.
- SemanticInputMap.lean: kernel checked generic Fin m -> Option (Fin n) input substitution. Produces a monotone n-input circuit with exactly substituted semantics and no larger size, assuming the substituted function is nonconstant. SHA25665ebee4262acdfd68ecbecbfc50ec8fa630756750a80eeec082a49450f11f2b3.
- SemanticPetersenDeletion.lean and its suffix are UNCOMPILED drafts: explicit ten vertex deletion relabelings, finite canonical9cofactor identity, and transport consumers. No build was started before root pause.
- Current full goal remains open. First AND is not excluded by floor16 plus three deletions: equality19=16+3 remains. Avoid assuming signed-minimum rewrites preserve ordinary gate cost.
- All complete build logs are under /tmp/oec/pequalnp-pilot-104/semantic2590-{restriction,charges,inputmap}.{stdout,stderr}. Three completed artifacts have exit0, no errors; inherited simp suggestions only.
