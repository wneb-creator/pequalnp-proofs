import H8Tail4352
import H8Tail4480
namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail
lemma checked (i : Fin 5230) (lower : 4352 ≤ i.val) (upper : i.val < 4608) :
    Replay.DirectMode.Packed.checkNode i = true := by
  have blocks : ∀ q : Fin 2, Replay.DirectMode.Packed.slice
      (4352+128*q.val) (min 128 (256-128*q.val)) = true := by
    intro q
    fin_cases q
    · exact c4352
    · exact c4480
  exact Replay.DirectMode.Packed.blocks_sound 4352 256 128 2 (by decide) (by decide)
    blocks i lower upper
end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail
