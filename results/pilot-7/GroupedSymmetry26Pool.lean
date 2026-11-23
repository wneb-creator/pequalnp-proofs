import GroupedSymmetryProbe
namespace PEqualNP.Outside.L_meta_982_aux.SymmetryProbe26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkPool : pool.all (fun a => (pool.map (Finite.Symmetry.GroupedProbe.fast 13 (k+k) p4)).contains a) = true := by decide +kernel
end PEqualNP.Outside.L_meta_982_aux.SymmetryProbe26
