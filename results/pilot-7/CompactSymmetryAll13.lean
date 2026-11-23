import CompactSymmetryData
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
open PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c13Good : ∀ p ∈ c13Perms, Symmetry.Good c13K c13F p :=
  Symmetry.checked_actions (c13Gens.getD · []) (by decide +kernel)
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
