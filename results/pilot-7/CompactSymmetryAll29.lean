import CompactSymmetryData
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
open PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c29Good : ∀ p ∈ c29Perms, Symmetry.Good c29K c29F p :=
  Symmetry.checked_actions (c29Gens.getD · []) (by decide +kernel)
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
