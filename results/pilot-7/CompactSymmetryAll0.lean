import CompactSymmetryData
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
open PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0Good : ∀ p ∈ c0Perms, Symmetry.Good c0K c0F p :=
  Symmetry.checked_actions (c0Gens.getD · []) (by decide +kernel)
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
