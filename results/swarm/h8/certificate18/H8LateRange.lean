import H8TailRange
import H8Range

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail

lemma checked_late (i : Fin 5230) (lower : 4352 ≤ i.val) :
    Replay.DirectMode.Packed.checkNode i = true := by
  by_cases upper : i.val < 4608
  · exact checked i lower upper
  · exact Helper8.checked i (by omega)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.Helper8Tail
