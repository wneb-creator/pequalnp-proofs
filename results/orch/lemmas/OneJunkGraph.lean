import Mathlib

namespace PEqualNP.Outside.L_meta_4675.OneJunkGraph

lemma two_column_edges {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (q : Fin p) (b₀ b₁ : Fin l)
    (hq : q ∈ A) (hb : b₀ ≠ b₁)
    (hstar : ∀ a ∈ A, (a, b₁) ∈ E) (hex : (q, b₀) ∈ E) :
    E ∩ (A ×ˢ {b₀, b₁}) = (A ×ˢ {b₁}) ∪ {(q, b₀)} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_union]
  constructor
  · rintro ⟨he, ha, hb' | hb'⟩
    · subst b
      have haq : a = q := by
        by_contra hne
        exact hC4 a q b₀ b₁ hne hb ⟨he, hstar a ha, hex, hstar q hq⟩
      exact Or.inr (by simp [haq])
    · exact Or.inl ⟨ha, hb'⟩
  · rintro (⟨ha, hb'⟩ | hab)
    · subst b
      exact ⟨hstar a ha, ha, Or.inr rfl⟩
    · cases hab
      exact ⟨hex, hq, Or.inl rfl⟩

lemma cross_triples_iff {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A Q : Finset (Fin p)) (B : Finset (Fin l)) :
    (∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) ↔
      ∀ b ∈ B, (∀ a ∈ A, (a, b) ∈ E) ∨ (∀ q ∈ Q, (q, b) ∈ E) := by
  classical
  constructor
  · intro h b hb
    by_cases hA : ∀ a ∈ A, (a, b) ∈ E
    · exact Or.inl hA
    · right
      push Not at hA
      obtain ⟨a, ha, hab⟩ := hA
      intro q hq
      exact (h a ha b hb q hq).resolve_left hab
  · intro h a ha b hb q hq
    rcases h b hb with hA | hQ
    · exact Or.inl (hA a ha)
    · exact Or.inr (hQ q hq)

end PEqualNP.Outside.L_meta_4675.OneJunkGraph
