import CompactSymmetryData
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
open PEqualNP.Outside.L_meta_982_aux.Finite
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c26Good : ∀ p ∈ c26Perms, Symmetry.Good c26K c26F p :=
  Symmetry.checked_actions (fun i => if i = 1 then c26Perms.getD 24 [] else c26Gens.getD i []) (by decide +kernel)
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
