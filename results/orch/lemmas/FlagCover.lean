import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.FlagCover

def flag {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (x : α → Bool) (y : β → Bool) : Bool :=
  decide ((∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, y b = true))

lemma active_neighbourhood_witness {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) (A : ι → Finset α) (B : ι → Finset β)
    (F : (ι → Bool) → Bool)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (a : α) (b : β)
    (hpair : F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∃ i, a ∈ A i ∧ b ∈ B i ∧ ∀ a' ∈ A i, R a' b := by
  classical
  by_contra hn
  have hflags : ∀ i, decide (a ∈ A i ∧ b ∈ B i) = true →
      flag (A i) (B i) (fun a' => decide (¬ R a' b))
        (fun b' => decide (b' = b)) = true := by
    intro i hi
    have hai : a ∈ A i ∧ b ∈ B i := of_decide_eq_true hi
    have hw : ∃ a' ∈ A i, ¬ R a' b := by
      by_contra hw
      apply hn
      refine ⟨i, hai.1, hai.2, ?_⟩
      intro a' ha'
      by_contra hR
      exact hw ⟨a', ha', hR⟩
    obtain ⟨a', ha', hR⟩ := hw
    apply decide_eq_true
    exact ⟨⟨a', ha', by simp [hR]⟩, ⟨b, hai.2, by simp⟩⟩
  have hf := hmono _ _ hflags hpair
  obtain ⟨a', b', hR, hx, hy⟩ := hsound _ _ hf
  have hb' : b' = b := by simpa using hy
  subst b'
  have hnR : ¬ R a' b := by simpa using hx
  exact hnR hR

lemma clean_rectangle_cover {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (A : ι → Finset α) (B : ι → Finset β) (F : (ι → Bool) → Bool)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (hcomplete : ∀ a b, R a b → F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∀ a b, R a b ↔ ∃ i, a ∈ A i ∧ b ∈ (B i).filter (fun b => ∀ a' ∈ A i, R a' b) := by
  intro a b
  constructor
  · intro hab
    obtain ⟨i, hai, hbi, hRi⟩ := active_neighbourhood_witness R A B F hmono hsound a b
      (hcomplete a b hab)
    exact ⟨i, hai, Finset.mem_filter.mpr ⟨hbi, hRi⟩⟩
  · rintro ⟨i, hai, hbi⟩
    exact (Finset.mem_filter.mp hbi).2 a hai

lemma cleaned_line_side_card_le_one {α β : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : Finset α) (B : Finset β) (hA : 1 < A.card) :
    (B.filter fun b => ∀ a ∈ A, R a b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro b hb b' hb'
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp hA
  by_contra hbb'
  have hR := (Finset.mem_filter.mp hb).2
  have hR' := (Finset.mem_filter.mp hb').2
  exact hfour a a' b b' haa' hbb'
    ⟨hR a ha, hR' a ha, hR a' ha', hR' a' ha'⟩

lemma clean_star_cover {α β ι : Type*} [DecidableEq α] [DecidableEq β]
    (R : α → β → Prop) [DecidableRel R]
    (hfour : ∀ a a' b b', a ≠ a' → b ≠ b' →
      ¬ (R a b ∧ R a b' ∧ R a' b ∧ R a' b'))
    (A : ι → Finset α) (B : ι → Finset β) (F : (ι → Bool) → Bool)
    (hbig : ∀ i, 1 < (A i).card)
    (hmono : ∀ u v, (∀ i, u i = true → v i = true) → F u = true → F v = true)
    (hsound : ∀ (x : α → Bool) (y : β → Bool),
      F (fun i => flag (A i) (B i) x y) = true →
      ∃ a b, R a b ∧ x a = true ∧ y b = true)
    (hcomplete : ∀ a b, R a b → F (fun i => decide (a ∈ A i ∧ b ∈ B i)) = true) :
    ∃ D : ι → Finset β,
      (∀ i, D i ⊆ B i ∧ (D i).card ≤ 1) ∧
      (∀ a b, R a b ↔ ∃ i, a ∈ A i ∧ b ∈ D i) := by
  refine ⟨fun i => (B i).filter (fun b => ∀ a ∈ A i, R a b), ?_, ?_⟩
  · intro i
    exact ⟨Finset.filter_subset _ _, cleaned_line_side_card_le_one R hfour (A i) (B i) (hbig i)⟩
  · exact clean_rectangle_cover R A B F hmono hsound hcomplete

end PEqualNP.Outside.L_meta_4675.FlagCover
