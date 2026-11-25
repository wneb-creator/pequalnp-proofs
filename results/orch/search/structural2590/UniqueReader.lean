import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590

open PEqualNP.CircuitLowerBounds

lemma unique_reader_split (gs : List Gate) (w : ℕ)
    (single : (gs.flatMap Gate.inputs).count w = 1) :
    ∃ before after : List Gate, ∃ g : Gate,
      gs = before ++ g :: after ∧ g.inputs.count w = 1 ∧
        ∀ h ∈ before ++ after, w ∉ h.inputs := by
  have present : w ∈ gs.flatMap Gate.inputs := List.count_pos_iff.mp (by omega)
  obtain ⟨g, hg, hi⟩ := List.mem_flatMap.mp present
  obtain ⟨before, after, rfl⟩ := List.append_of_mem hg
  have pos : 0 < g.inputs.count w := List.count_pos_iff.mpr hi
  simp only [List.flatMap_append, List.flatMap_cons, List.count_append] at single
  have left : (before.flatMap Gate.inputs).count w = 0 := by omega
  have right : (after.flatMap Gate.inputs).count w = 0 := by omega
  refine ⟨before, after, g, rfl, by omega, ?_⟩
  intro h hh hw
  rcases List.mem_append.mp hh with hb | ha
  · exact List.count_eq_zero.mp left (List.mem_flatMap.mpr ⟨h, hb, hw⟩)
  · exact List.count_eq_zero.mp right (List.mem_flatMap.mpr ⟨h, ha, hw⟩)

end PEqualNP.Outside.L_meta_2590
