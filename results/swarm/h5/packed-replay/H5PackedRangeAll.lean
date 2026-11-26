import H5PackedRange3072
import H5PackedRange3136
import H5PackedRange3200
import H5PackedRange3264
import H5PackedRange3328
import H5PackedRange3392
import H5PackedRange3456
import H5PackedRange3520
import H5PackedRange3584
import H5PackedRange3648
import H5PackedRange3712
import H5PackedRange3776

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5

lemma rangeAll : block 3072 768 := by
  have b0 : block 3072 128 := block_add 3072 64 64 range3072 range3136
  have b1 : block 3200 128 := block_add 3200 64 64 range3200 range3264
  have b2 : block 3328 128 := block_add 3328 64 64 range3328 range3392
  have b3 : block 3456 128 := block_add 3456 64 64 range3456 range3520
  have b4 : block 3584 128 := block_add 3584 64 64 range3584 range3648
  have b5 : block 3712 128 := block_add 3712 64 64 range3712 range3776
  have c0 : block 3072 256 := block_add 3072 128 128 b0 b1
  have c1 : block 3328 256 := block_add 3328 128 128 b2 b3
  have c2 : block 3584 256 := block_add 3584 128 128 b4 b5
  have d : block 3072 512 := block_add 3072 256 256 c0 c1
  exact block_add 3072 512 256 d c2

lemma checkedRange (i : Fin 5230) (lo : 3072 ≤ i.val) (hi : i.val < 3840) :
    checkNode i = true := by
  have offset : i.val - 3072 < 768 := by omega
  have checked := rangeAll ⟨i.val - 3072, offset⟩
  have noWrap : 3072 + (i.val - 3072) < 5230 := by omega
  have index_eq : Fin.ofNat 5230 (3072 + (i.val - 3072)) = i := by
    apply Fin.ext
    change (3072 + (i.val - 3072)) % 5230 = i.val
    rw [Nat.mod_eq_of_lt noWrap]
    omega
  change checkNode (Fin.ofNat 5230 (3072 + (i.val - 3072))) = true at checked
  rw [index_eq] at checked
  exact checked

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Replay.DirectMode.Packed.H5
