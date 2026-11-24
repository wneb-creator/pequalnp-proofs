import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5282_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

lemma erase_mono (n m p : ℕ) (C : Circuit) (hC : Monotone2 C) :
    Monotone2 (eraseGate n C m p) := by
  by_cases hm : m < C.gates.length
  · intro g hg
    simp only [eraseGate, if_pos hm] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hC _ (List.mem_of_mem_take hg)
    · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      obtain ⟨hop, hlen⟩ := hC _ (List.mem_of_mem_drop hg0)
      exact ⟨hop, by simpa using hlen⟩
  · simpa only [eraseGate, if_neg hm] using hC

lemma erase_size (n m p : ℕ) (C : Circuit) (hm : m < C.size) :
    (eraseGate n C m p).size + 1 = C.size := by
  have hm' : m < C.gates.length := hm
  simp only [eraseGate, if_pos hm', Circuit.size, List.length_append,
    List.length_take, List.length_map, List.length_drop]
  omega

end PEqualNP.Outside.L_meta_5282_aux
