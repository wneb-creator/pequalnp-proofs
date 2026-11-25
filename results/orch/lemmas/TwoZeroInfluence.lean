import PetersenEighteenExtension

namespace PEqualNP.Outside.L_meta_2373

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma two_zero_separator : ∀ a b c : Fin 10, ∃ d : Fin 10,
    d ≠ a ∧ d ≠ b ∧ d ≠ c ∧ edge (pairInput a d) = true := by
  decide +kernel

namespace Live1024

lemma two_zero_influence_rows (a b c : Fin 10) (hab : a ≠ b) (hac : a ≠ c) :
    ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (inputs.getD b.val zero) = false ∧
      bit s (inputs.getD b.val zero) = false ∧
      bit r (inputs.getD c.val zero) = false ∧
      bit s (inputs.getD c.val zero) = false ∧
      bit r graph ≠ bit s graph := by
  obtain ⟨d, hda, hdb, hdc, he⟩ := two_zero_separator a b c
  refine ⟨singleRow d, pairRow a d, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hia
    rw [singleRow_input, pairRow_input]
    simp [singleInput, pairInput, hia]
  · rw [singleRow_input]
    simp [singleInput, Ne.symm hdb]
  · rw [pairRow_input]
    simp [pairInput, Ne.symm hab, Ne.symm hdb]
  · rw [singleRow_input]
    simp [singleInput, Ne.symm hdc]
  · rw [pairRow_input]
    simp [pairInput, Ne.symm hac, Ne.symm hdc]
  · rw [singleRow_graph, pairRow_graph, singleton_no_edge, he]
    decide

end Live1024
end PEqualNP.Outside.L_meta_2373
