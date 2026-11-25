import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

lemma first_proper_binary_used {k S} (run : Live true target k S)
    (raw : ∀ a ∈ S, a ∈ pins) :
    ∃ j a b d T, k = j + 1 ∧ a ∈ pins ∧ b ∈ pins ∧ a ≠ b ∧ d < 4 ∧
      Live true target j T ∧ bin d a b ∈ T ∧ ∀ c ∈ T, c ∈ pins ++ [bin d a b] := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have hm := raw target (by simp)
    have hn : target ∉ pins := by decide +kernel
    exact (hn hm).elim
  | succ j =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,_,tail⟩ := run
    refine ⟨j,a,b,d,insert (bin d a b) U,rfl,raw a (by simp),raw b (by simp),hab,?_,tail,by simp,?_⟩
    · rcases hd with h | ⟨_,h⟩ <;> omega
    · intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ (raw c (by simp [hc]))

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
