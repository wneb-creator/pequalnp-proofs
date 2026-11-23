import CompactSymmetryData
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
open PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c25Good : ∀ p ∈ c25Perms, Symmetry.Good c25K c25F p :=
  Symmetry.checked_actions (c25Gens.getD · []) (by decide +kernel)
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
