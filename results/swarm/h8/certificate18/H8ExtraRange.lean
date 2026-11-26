import H8Extra256
import H8Extra384
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Extra
lemma checked (i : Fin 5230) (lower : 256 ≤ i.val) (upper : i.val < 512) :
    Replay.DirectMode.Packed.checkNode i = true := by
  have blocks : ∀ q : Fin 2, Replay.DirectMode.Packed.slice
      (256+128*q.val) (min 128 (256-128*q.val)) = true := by
    intro q
    fin_cases q
    · exact c256
    · exact c384
  exact Replay.DirectMode.Packed.blocks_sound 256 256 128 2 (by decide) (by decide)
    blocks i lower upper
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Extra
