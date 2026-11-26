import H5PackedRange3840
import H5PackedRange3904
import H5PackedRange3968
import H5PackedRange4032
import H5PackedRange4096
import H5PackedRange4160
import H5PackedRange4224
import H5PackedRange4288

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5

lemma rangeExtra : block 3840 512 := by
  have b0 : block 3840 128 := block_add 3840 64 64 range3840 range3904
  have b1 : block 3968 128 := block_add 3968 64 64 range3968 range4032
  have b2 : block 4096 128 := block_add 4096 64 64 range4096 range4160
  have b3 : block 4224 128 := block_add 4224 64 64 range4224 range4288
  have c0 : block 3840 256 := block_add 3840 128 128 b0 b1
  have c1 : block 4096 256 := block_add 4096 128 128 b2 b3
  exact block_add 3840 256 256 c0 c1

lemma checkedExtraRange (i : Fin 5230) (lo : 3840 ≤ i.val) (hi : i.val < 4352) :
    checkNode i = true := by
  have offset : i.val - 3840 < 512 := by omega
  have checked := rangeExtra ⟨i.val - 3840, offset⟩
  have noWrap : 3840 + (i.val - 3840) < 5230 := by omega
  have index_eq : Fin.ofNat 5230 (3840 + (i.val - 3840)) = i := by
    apply Fin.ext
    change (3840 + (i.val - 3840)) % 5230 = i.val
    rw [Nat.mod_eq_of_lt noWrap]
    omega
  change checkNode (Fin.ofNat 5230 (3840 + (i.val - 3840))) = true at checked
  rw [index_eq] at checked
  exact checked

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
