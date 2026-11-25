import CanonicalSampleData
import GeometryFlags

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sample_positive_bits : ∀ a : Fin 52, ∀ i : Fin 26,
    (sampleInputMasks i).testBit a.val = Flags.input a i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma sample_negative_bits_0 : ∀ r : AllRows.R,
    (sampleInputMasks 0).testBit (52 + 13 * r.1.val + r.2.val) = AllRows.row r 0 := by
  decide +kernel

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
