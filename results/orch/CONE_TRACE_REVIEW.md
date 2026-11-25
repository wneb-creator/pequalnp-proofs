Independent root review: pruning cone embedding
Result: PASS; source proof read in full.
Exact dependency block: MaskingNext.lean
Exact dependency block: OneJunk.lean
Exact dependency block: OrReachAPI.lean
Exact dependency block: PruningCost.lean
Exact dependency block: PruningTrace.lean
Exact dependency block: ConeAPI.lean
Exact dependency block: ConeTrace.lean
ConeAPI.lean SHA256 a5b8b3ff76e6ebea2096f57ecc6c372290ac8d6df3252ecf72201c1f1395c5a1
ConeTrace.lean SHA256 27b0a0e9923e18f2403e8a53d6cb2b9242bc4ddea4d645a721819a75a495ca1d
GateTrace strictly orders original indices, preserves operations and source aliases, and transports every retained wire-cone relation into the original circuit.
The forced gate cannot be in the origin image because its alias is none; pairwise injectivity follows from strict index ordering.
pruned_andPairs_le embeds both AND endpoints and their cone relation into the original finite pair set. No strict restoration measure or final gap theorem is claimed.
Author Lean compilation exited0; complete cone-trace-lean.log retained.
