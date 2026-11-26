import H4Range2304_2307
import H4Range2308_2339

namespace PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay

lemma range_checked {first count : Nat}
    (h : ((List.range' first count).all fun n =>
      Replay.DirectMode.Packed.checkNode (Fin.ofNat 5230 n)) = true)
    (i : Fin 5230) (lower : first ≤ i.val) (upper : i.val < first + count) :
    Replay.DirectMode.Packed.checkNode i = true := by
  have member : i.val ∈ List.range' first count := List.mem_range'_1.mpr ⟨lower, upper⟩
  have checked := List.all_eq_true.mp h i.val member
  have roundtrip : Fin.ofNat 5230 i.val = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  simpa only [roundtrip] using checked

lemma checked_2304_2339 (i : Fin 5230) (lower : 2304 ≤ i.val) (upper : i.val ≤ 2339) :
    Replay.DirectMode.Packed.checkNode i = true := by
  by_cases first : i.val ≤ 2307
  · exact range_checked h4_2304_2307 i lower (by omega)
  · exact range_checked h4_2308_2339 i (by omega) (by omega)

end PEqualNP.Outside.L_meta_2373_aux.Cert18.H4Replay
