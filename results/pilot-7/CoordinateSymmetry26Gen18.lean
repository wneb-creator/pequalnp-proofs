import CoordinateSymmetry
import LinearSymmetryData26
namespace PEqualNP.Outside.L_meta_982_aux.SymmetryProbe26
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checkDerived18 : Finite.Symmetry.Grouped.Check k 13 pool (Finite.Symmetry.Coordinates.full k 7 13 (Finite.Symmetry.Coordinates.rows (k+k) (pool.drop 2)) [0,3,4,2,1,5,6]) = true := by decide +kernel
end PEqualNP.Outside.L_meta_982_aux.SymmetryProbe26
