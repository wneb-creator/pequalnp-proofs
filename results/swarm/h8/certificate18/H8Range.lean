import H8Chunk4608
import H8Chunk4736
import H8Chunk4864
import H8Chunk4992
import H8Chunk5120
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8
lemma checked (i : Fin 5230) (lower : 4608 ≤ i.val) :
    Replay.DirectMode.Packed.checkNode i = true := by
  have blocks : ∀ q : Fin 5, Replay.DirectMode.Packed.slice
      (4608+128*q.val) (min 128 (622-128*q.val)) = true := by
    intro q
    fin_cases q
    · exact c4608
    · exact c4736
    · exact c4864
    · exact c4992
    · exact c5120
  exact Replay.DirectMode.Packed.blocks_sound 4608 622 128 5 (by decide) (by decide)
    blocks i lower (by omega)
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8
