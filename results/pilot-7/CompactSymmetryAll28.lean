import CompactSymmetryData
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
open PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c28Good : ∀ p ∈ c28Perms, Symmetry.Good c28K c28F p :=
  Symmetry.checked_actions (c28Gens.getD · []) (by decide +kernel)
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
