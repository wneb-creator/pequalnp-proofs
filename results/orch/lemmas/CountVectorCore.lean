import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.CountVector

variable {α β Ω : Type} [DecidableEq α] [DecidableEq β]

def count (tag : α → β) (A : Finset α) (j : β) : Nat :=
  (A.filter (fun r => tag r = j)).card

lemma count_singleton (tag : α → β) (r : α) (j : β) :
    count tag {r} j = if tag r = j then 1 else 0 := by
  by_cases h : tag r = j
  · have eq : ({r} : Finset α).filter (fun x => tag x = j) = {r} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · exact fun hx => hx.1
      · intro hx
        subst x
        exact ⟨rfl, h⟩
    simp only [count, eq, Finset.card_singleton, ite_eq_left h]
  · have eq : ({r} : Finset α).filter (fun x => tag x = j) = ∅ := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, hx⟩
        exact False.elim (h hx)
      · intro hx
        exact False.elim (by simpa using hx)
    simp only [count, eq, Finset.card_empty, ite_eq_right h]

lemma count_mono (tag : α → β) {A B : Finset α} (sub : A ⊆ B) (j : β) :
    count tag A j ≤ count tag B j := by
  apply Finset.card_le_card
  intro r hr
  obtain ⟨ha, hj⟩ := Finset.mem_filter.mp hr
  exact Finset.mem_filter.mpr ⟨sub ha, hj⟩

lemma count_union (tag : α → β) (A B : Finset α) (dis : Disjoint A B) (j : β) :
    count tag (A ∪ B) j = count tag A j + count tag B j := by
  have split : (A ∪ B).filter (fun r => tag r = j) =
      A.filter (fun r => tag r = j) ∪ B.filter (fun r => tag r = j) := by
    ext r
    simp [or_and_right]
  have filtered : Disjoint (A.filter (fun r => tag r = j))
      (B.filter (fun r => tag r = j)) :=
    dis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  exact (congrArg Finset.card split).trans (Finset.card_union_of_disjoint filtered)

lemma count_sdiff (tag : α → β) (roots A : Finset α) (sub : A ⊆ roots) (j : β) :
    count tag (roots \ A) j = count tag roots j - count tag A j := by
  have split : (roots \ A).filter (fun r => tag r = j) =
      roots.filter (fun r => tag r = j) \ A.filter (fun r => tag r = j) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  have filtered : A.filter (fun r => tag r = j) ⊆ roots.filter (fun r => tag r = j) := by
    intro r hr
    obtain ⟨ha, hj⟩ := Finset.mem_filter.mp hr
    exact Finset.mem_filter.mpr ⟨sub ha, hj⟩
  exact (congrArg Finset.card split).trans (Finset.card_sdiff_of_subset filtered)

lemma outside_iff (tag : α → β) (roots A : Finset α) (sub : A ⊆ roots) (j : β) :
    (∃ r ∈ roots, r ∉ A ∧ tag r = j) ↔ count tag A j < count tag roots j := by
  have difference := count_sdiff tag roots A sub j
  constructor
  · rintro ⟨r, hr, ha, hj⟩
    have positive : 0 < count tag (roots \ A) j := by
      apply Finset.card_pos.mpr
      exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hr, ha⟩, hj⟩⟩
    omega
  · intro lt
    have positive : 0 < count tag (roots \ A) j := by omega
    obtain ⟨r, hr⟩ := Finset.card_pos.mp positive
    obtain ⟨hr, hj⟩ := Finset.mem_filter.mp hr
    obtain ⟨hr, ha⟩ := Finset.mem_sdiff.mp hr
    exact ⟨r, hr, ha, hj⟩

lemma outside_column_iff (tag : α → β) (roots A : Finset α) (sub : A ⊆ roots)
    (col : β → Set Ω) (o : Ω) :
    (∃ r ∈ roots, r ∉ A ∧ o ∈ col (tag r)) ↔
      ∃ j, count tag A j < count tag roots j ∧ o ∈ col j := by
  constructor
  · rintro ⟨r, hr, ha, ho⟩
    exact ⟨tag r, (outside_iff tag roots A sub (tag r)).mp ⟨r, hr, ha, rfl⟩, ho⟩
  · rintro ⟨j, hj, ho⟩
    obtain ⟨r, hr, ha, eq⟩ := (outside_iff tag roots A sub j).mpr hj
    exact ⟨r, hr, ha, eq.symm ▸ ho⟩

lemma outside_absent_iff (tag : α → β) (roots A : Finset α) (sub : A ⊆ roots)
    (col : β → Set Ω) (o : Ω) :
    (∀ r ∈ roots, r ∉ A → o ∉ col (tag r)) ↔
      ∀ j, count tag A j < count tag roots j → o ∉ col j := by
  constructor
  · intro absent j hj ho
    obtain ⟨r, hr, ha, eq⟩ := (outside_iff tag roots A sub j).mpr hj
    exact absent r hr ha (eq.symm ▸ ho)
  · intro absent r hr ha ho
    exact absent (tag r) ((outside_iff tag roots A sub (tag r)).mp ⟨r, hr, ha, rfl⟩) ho

lemma count_image {γ : Type} [DecidableEq γ] (tag : α → β) (next : γ → β)
    (f : α → γ) (injective : Function.Injective f) (same : ∀ r, next (f r) = tag r)
    (A : Finset α) (j : β) : count next (A.image f) j = count tag A j := by
  have eq : (A.image f).filter (fun r => next r = j) =
      (A.filter (fun r => tag r = j)).image f := by
    ext x
    constructor
    · intro hx
      obtain ⟨hx, hj⟩ := Finset.mem_filter.mp hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, (same r).symm.trans hj⟩, rfl⟩
    · intro hx
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨hr, hj⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r, hr, rfl⟩, (same r).trans hj⟩
  exact (congrArg Finset.card eq).trans (Finset.card_image_of_injective _ injective)

lemma count_sum [Fintype β] (tag : α → β) (A : Finset α) :
    (∑ j, count tag A j) = A.card := by
  induction A using Finset.induction_on with
  | empty => simp [count]
  | @insert a A ha ih =>
    have dis : Disjoint ({a} : Finset α) A := by simpa using ha
    have eq : insert a A = {a} ∪ A := by ext r; simp
    simp_rw [eq, count_union tag {a} A dis]
    rw [Finset.sum_add_distrib, ih]
    simp_rw [count_singleton]
    simp [eq_comm, ha, Nat.add_comm]

end PEqualNP.Outside.L_meta_2373.CountVector
