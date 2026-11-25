import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675_aux

lemma clean_product_neighbourhood_witness {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop) (I : Finset ι) (A : ι → Finset α) (B : ι → Finset β)
    (hclean : ∀ (x : α → Bool) (y : β → Bool),
      (∀ i ∈ I, ∃ a ∈ A i, x a = true) →
      (∀ i ∈ I, ∃ b ∈ B i, y b = true) →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (b : β) (hb : ∀ i ∈ I, b ∈ B i) :
    ∃ i ∈ I, ∀ a ∈ A i, R a b := by
  classical
  by_contra hn
  have hw : ∀ i ∈ I, ∃ a ∈ A i, ¬ R a b := by
    intro i hi
    by_contra ha
    apply hn
    refine ⟨i, hi, ?_⟩
    intro a hai
    by_contra hr
    exact ha ⟨a, hai, hr⟩
  obtain ⟨a, b', hab, hax, hby⟩ := hclean
    (fun a => decide (¬ R a b)) (fun b' => decide (b' = b))
    (fun i hi => by
      obtain ⟨a, hai, har⟩ := hw i hi
      exact ⟨a, hai, by simp [har]⟩)
    (fun i hi => ⟨b, hb i hi, by simp⟩)
  have hb' : b' = b := by simpa using hby
  subst b'
  have hnot : ¬ R a b := by simpa using hax
  exact hnot hab

lemma large_set_common_neighbour_unique {α β : Type*}
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : Finset α) (hA : 1 < A.card)
    (b b' : β) (hb : ∀ a ∈ A, R a b) (hb' : ∀ a ∈ A, R a b') : b = b' := by
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp hA
  by_contra hbb'
  exact hfour a a' b b' haa' hbb' ⟨hb a ha, hb' a ha, hb a' ha', hb' a' ha'⟩

lemma large_set_neighbourhood_cover_bound {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (I : Finset ι) (A : ι → Finset α) (T : Finset β)
    (hA : ∀ i ∈ I, 1 < (A i).card)
    (hcover : ∀ b ∈ T, ∃ i ∈ I, ∀ a ∈ A i, R a b) : T.card ≤ I.card := by
  classical
  let U : ι → Finset β := fun i => T.filter fun b => ∀ a ∈ A i, R a b
  have hsub : T ⊆ I.biUnion U := by
    intro b hb
    obtain ⟨i, hi, hAi⟩ := hcover b hb
    exact Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_filter.mpr ⟨hb, hAi⟩⟩
  have hU : ∀ i ∈ I, (U i).card ≤ 1 := by
    intro i hi
    apply Finset.card_le_one.mpr
    intro b hb b' hb'
    exact large_set_common_neighbour_unique R hfour (A i) (hA i hi) b b'
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hb').2
  calc
    T.card ≤ (I.biUnion U).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ I, (U i).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ I, (1 : ℕ) := Finset.sum_le_sum hU
    _ = I.card := by simp

lemma clean_product_common_lines_bound {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (I : Finset ι) (A : ι → Finset α) (B : ι → Finset β) (T : Finset β)
    (hA : ∀ i ∈ I, 1 < (A i).card)
    (hT : ∀ b ∈ T, ∀ i ∈ I, b ∈ B i)
    (hclean : ∀ (x : α → Bool) (y : β → Bool),
      (∀ i ∈ I, ∃ a ∈ A i, x a = true) →
      (∀ i ∈ I, ∃ b ∈ B i, y b = true) →
      ∃ a b, R a b ∧ x a = true ∧ y b = true) : T.card ≤ I.card := by
  apply large_set_neighbourhood_cover_bound R hfour I A T hA
  intro b hb
  exact clean_product_neighbourhood_witness R I A B hclean b (hT b hb)

lemma clean_product_common_points_bound {α β ι : Type*} [DecidableEq ι]
    (R : α → β → Prop)
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (I : Finset ι) (A : ι → Finset α) (B : ι → Finset β) (T : Finset α)
    (hB : ∀ i ∈ I, 1 < (B i).card)
    (hT : ∀ a ∈ T, ∀ i ∈ I, a ∈ A i)
    (hclean : ∀ (x : α → Bool) (y : β → Bool),
      (∀ i ∈ I, ∃ a ∈ A i, x a = true) →
      (∀ i ∈ I, ∃ b ∈ B i, y b = true) →
      ∃ a b, R a b ∧ x a = true ∧ y b = true) : T.card ≤ I.card := by
  have hfour' : ∀ b b' a a', b ≠ b' → a ≠ a' →
      ¬ (R a b ∧ R a' b ∧ R a b' ∧ R a' b') := by
    intro b b' a a' hbb' haa' h
    exact hfour a a' b b' haa' hbb' ⟨h.1, h.2.2.1, h.2.1, h.2.2.2⟩
  apply clean_product_common_lines_bound (fun b a => R a b) hfour' I B A T hB hT
  intro y x hY hX
  obtain ⟨a, b, hab, hax, hby⟩ := hclean x y hX hY
  exact ⟨b, a, hab, hby, hax⟩

end PEqualNP.Outside.L_meta_4675_aux
