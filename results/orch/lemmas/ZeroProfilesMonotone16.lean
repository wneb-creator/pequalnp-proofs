import NineMonotoneExtension
import SliceProfiles

namespace PEqualNP.Outside.L_meta_2373.ZeroProfiles

open PEqualNP.Outside.L_meta_2373

lemma slice_monotone16 (v : Fin 10) :
    Live1024.Slice false Live1024.inputs Live1024.graph (domain v) 16 := by
  apply Live1024.Slice_from_nine (rowMap v) Live1024.inputs Live1024.graph (domain v)
    NineSigned.inputs NineSigned.graph 16
  · exact rows_domain v
  · funext r
    exact rowMap_graph v r
  · intro a ha
    rw [← Live1024.input_list] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact rows_available v i
  · exact NineSigned.graph_proper
  · exact NineSigned.nine_monotone_reach_lower


lemma slice_mode_bound (u : Bool) (v : Fin 10) :
    Live1024.Slice u Live1024.inputs Live1024.graph (domain v) (if u then 15 else 16) := by
  cases u with
  | false => exact slice_monotone16 v
  | true => exact slice v

end PEqualNP.Outside.L_meta_2373.ZeroProfiles
