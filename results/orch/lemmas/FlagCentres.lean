import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.FlagCover

lemma finite_centres {α β : Type*} [DecidableEq α] [DecidableEq β] [Inhabited β]
    (R : α → β → Prop) (G : Finset ℕ) (A : ℕ → Finset α) (D : ℕ → Finset β)
    (hcard : ∀ i ∈ G, (D i).card ≤ 1)
    (hrect : ∀ i ∈ G, ∀ a ∈ A i, ∀ b ∈ D i, R a b)
    (hcover : ∀ a b, R a b → ∃ i ∈ G, a ∈ A i ∧ b ∈ D i) :
    ∃ (J : Finset ℕ) (c : ℕ → β),
      J ⊆ G ∧
      (∀ i ∈ J, D i = {c i}) ∧
      (∀ a b, R a b → ∃ i ∈ J, a ∈ A i ∧ b = c i) ∧
      (∀ i ∈ J, ∀ a ∈ A i, R a (c i)) := by
  classical
  let J := G.filter fun i => (D i).Nonempty
  let c : ℕ → β := fun i => if h : (D i).Nonempty then h.choose else default
  have hJ : ∀ i, i ∈ J ↔ i ∈ G ∧ (D i).Nonempty := by
    intro i
    exact Finset.mem_filter
  have hc : ∀ i ∈ J, c i ∈ D i := by
    intro i hi
    have hn := (hJ i).mp hi |>.2
    simp only [c, dif_pos hn]
    exact hn.choose_spec
  have hsingle : ∀ i ∈ J, D i = {c i} := by
    intro i hi
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hc i hi, fun b hb => Finset.card_le_one.mp
      (hcard i ((hJ i).mp hi).1) b hb (c i) (hc i hi)⟩
  refine ⟨J, c, Finset.filter_subset _ _, hsingle, ?_, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, hai, hbi⟩ := hcover a b hab
    have hiJ : i ∈ J := (hJ i).mpr ⟨hi, ⟨b, hbi⟩⟩
    refine ⟨i, hiJ, hai, ?_⟩
    rw [hsingle i hiJ] at hbi
    exact Finset.mem_singleton.mp hbi
  · intro i hi a hai
    exact hrect i ((hJ i).mp hi).1 a hai (c i) (hc i hi)

end PEqualNP.Outside.L_meta_4675.FlagCover
