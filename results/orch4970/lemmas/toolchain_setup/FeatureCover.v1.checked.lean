import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux.FeatureCover

def NoFour {p l : ℕ} (E : Finset (Fin p × Fin l)) : Prop :=
  ∀ a a' b b', a ≠ a' → b ≠ b' →
    ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E)

lemma feature_vertex {p l : ℕ} (E : Finset (Fin p × Fin l))
    (square_free : NoFour E) (Q : Finset (Fin p))
    (useful : ∃ a b, a ∈ Q ∧ ∀ a' ∈ Q, (a', b) ∈ E) :
    ∃ v : Fin (p + l), ∀ a b, a ∈ Q → (∀ a' ∈ Q, (a', b) ∈ E) →
      Fin.castAdd l a = v ∨ Fin.natAdd p b = v := by
  classical
  obtain ⟨a₀, b₀, ha₀, hb₀⟩ := useful
  by_cases singleton : ∀ a ∈ Q, a = a₀
  · refine ⟨Fin.castAdd l a₀, ?_⟩
    intro a b ha _
    exact Or.inl (congrArg (Fin.castAdd l) (singleton a ha))
  · push Not at singleton
    obtain ⟨a₁, ha₁, different⟩ := singleton
    refine ⟨Fin.natAdd p b₀, ?_⟩
    intro a b ha hb
    right
    have same : b = b₀ := by
      by_contra ne
      exact square_free a₀ a₁ b b₀ (Ne.symm different) ne
        ⟨hb a₀ ha₀, hb₀ a₀ ha₀, hb a₁ ha₁, hb₀ a₁ ha₁⟩
    exact congrArg (Fin.natAdd p) same

lemma point_features_cover {p l k : ℕ} (E : Finset (Fin p × Fin l))
    (square_free : NoFour E) (Q : Fin k → Finset (Fin p))
    (covers : ∀ a b, (a, b) ∈ E →
      ∃ i, a ∈ Q i ∧ ∀ a' ∈ Q i, (a', b) ∈ E) :
    ∃ S : Finset (Fin (p + l)), S.card ≤ k ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  let U : Finset (Fin k) := Finset.univ.filter fun i =>
    ∃ a b, a ∈ Q i ∧ ∀ a' ∈ Q i, (a', b) ∈ E
  have choose_vertex : ∀ i : {i // i ∈ U},
      ∃ v : Fin (p + l), ∀ a b, a ∈ Q i.val →
        (∀ a' ∈ Q i.val, (a', b) ∈ E) →
          Fin.castAdd l a = v ∨ Fin.natAdd p b = v := by
    intro i
    apply feature_vertex E square_free (Q i.val)
    exact (Finset.mem_filter.mp i.property).2
  choose vertex vertex_spec using choose_vertex
  let S : Finset (Fin (p + l)) := Finset.univ.image vertex
  refine ⟨S, ?_, ?_⟩
  · have small : S.card ≤ U.card := by
      simpa [S] using Finset.card_image_le (s := Finset.univ) (f := vertex)
    have bounded : U.card ≤ k := by
      calc
        U.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_le_card (by
          intro i _
          exact Finset.mem_univ i)
        _ = k := by simp
    exact small.trans bounded
  · intro a b hab
    obtain ⟨i, hai, hbi⟩ := covers a b hab
    have hi : i ∈ U := Finset.mem_filter.mpr ⟨Finset.mem_univ i, ⟨a, b, hai, hbi⟩⟩
    have mem : vertex ⟨i, hi⟩ ∈ S := Finset.mem_image.mpr
      ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    rcases vertex_spec ⟨i, hi⟩ a b hai hbi with h | h
    · exact Or.inl (h.symm ▸ mem)
    · exact Or.inr (h.symm ▸ mem)

end PEqualNP.Outside.L_meta_4970_aux.FeatureCover
