import H8ExtraRange
import H8Extra512
import H8Extra640
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Extra
lemma checked_early (i : Fin 5230) (lower : 256 ≤ i.val) (upper : i.val < 768) :
    Replay.DirectMode.Packed.checkNode i = true := by
  have blocks : ∀ q : Fin 4, Replay.DirectMode.Packed.slice
      (256+128*q.val) (min 128 (512-128*q.val)) = true := by
    intro q
    fin_cases q
    · exact c256
    · exact c384
    · exact c512
    · exact c640
  exact Replay.DirectMode.Packed.blocks_sound 256 512 128 4 (by decide) (by decide)
    blocks i lower upper
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Extra
