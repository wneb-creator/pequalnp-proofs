import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970

lemma empty_edges (p l : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ (∅ : Finset (Fin p × Fin l)) →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (∅ : Finset (Fin p × Fin l)).card + S.card ≤ C.size + 1 := by
  exact ⟨∅, by simp⟩

end PEqualNP.Outside.L_meta_4970
