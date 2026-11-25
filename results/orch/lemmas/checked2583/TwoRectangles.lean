import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.TwoRectangles

lemma one_side_incident {α β : Type} [DecidableEq α] [DecidableEq β]
    (I : α → β → Prop) (P₁ P₂ : Finset α) (L₁ L₂ : Finset β)
    (below : ∀ (X : Finset α) (Y : Finset β),
      (P₁ ∩ X).Nonempty → (P₂ ∩ X).Nonempty →
      (L₁ ∩ Y).Nonempty → (L₂ ∩ Y).Nonempty → ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (p : α) (hp₁ : p ∈ P₁) (hp₂ : p ∈ P₂) :
    (∀ l ∈ L₁, I p l) ∨ (∀ l ∈ L₂, I p l) := by
  classical
  by_cases first : ∀ l ∈ L₁, I p l
  · exact Or.inl first
  right
  by_contra second
  push Not at first second
  obtain ⟨l₁, hl₁, hn₁⟩ := first
  obtain ⟨l₂, hl₂, hn₂⟩ := second
  obtain ⟨u, hu, v, hv, incident⟩ := below {p} {l₁, l₂}
    ⟨p, by simp [hp₁]⟩ ⟨p, by simp [hp₂]⟩
    ⟨l₁, by simp [hl₁]⟩ ⟨l₂, by simp [hl₂]⟩
  have same : u = p := Finset.mem_singleton.mp hu
  subst u
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact hn₁ incident
  · exact hn₂ incident

lemma star_replacement {α β : Type} [DecidableEq α] [DecidableEq β]
    (I : α → β → Prop) (P₁ P₂ : Finset α) (L₁ L₂ : Finset β)
    (noRectangle : ∀ p p' l l', p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (below : ∀ (X : Finset α) (Y : Finset β),
      (P₁ ∩ X).Nonempty → (P₂ ∩ X).Nonempty →
      (L₁ ∩ Y).Nonempty → (L₂ ∩ Y).Nonempty → ∃ p ∈ X, ∃ l ∈ Y, I p l)
    (pointEdge : (P₁ ∩ P₂).Nonempty) (lineEdge : (L₁ ∩ L₂).Nonempty) :
    (∃ p, P₁ ∩ P₂ = {p} ∧ ((∀ l ∈ L₁, I p l) ∨ (∀ l ∈ L₂, I p l))) ∨
    (∃ l, L₁ ∩ L₂ = {l} ∧ ((∀ p ∈ P₁, I p l) ∨ (∀ p ∈ P₂, I p l))) := by
  classical
  have commonIncident : ∀ p ∈ P₁ ∩ P₂, ∀ l ∈ L₁ ∩ L₂, I p l := by
    intro p hp l hl
    have hp₁ := (Finset.mem_inter.mp hp).1
    have hp₂ := (Finset.mem_inter.mp hp).2
    have hl₁ := (Finset.mem_inter.mp hl).1
    have hl₂ := (Finset.mem_inter.mp hl).2
    obtain ⟨u, hu, v, hv, hit⟩ := below {p} {l}
      ⟨p, by simp [hp₁]⟩ ⟨p, by simp [hp₂]⟩
      ⟨l, by simp [hl₁]⟩ ⟨l, by simp [hl₂]⟩
    have hu' := Finset.mem_singleton.mp hu
    have hv' := Finset.mem_singleton.mp hv
    subst u
    subst v
    exact hit
  obtain ⟨p, hp⟩ := pointEdge
  obtain ⟨l, hl⟩ := lineEdge
  by_cases singleton : P₁ ∩ P₂ = {p}
  · exact Or.inl ⟨p, singleton,
      one_side_incident I P₁ P₂ L₁ L₂ below p
        (Finset.mem_inter.mp hp).1 (Finset.mem_inter.mp hp).2⟩
  have other : ∃ p' ∈ P₁ ∩ P₂, p' ≠ p := by
    by_contra! h
    apply singleton
    ext u
    rw [Finset.mem_singleton]
    constructor
    · exact h u
    · rintro rfl
      exact hp
  obtain ⟨p', hp', different⟩ := other
  have lineSingleton : L₁ ∩ L₂ = {l} := by
    ext v
    rw [Finset.mem_singleton]
    constructor
    · intro hv
      by_contra ne
      exact noRectangle p p' l v (Ne.symm different) (Ne.symm ne)
        ⟨commonIncident p hp l hl, commonIncident p hp v hv,
          commonIncident p' hp' l hl, commonIncident p' hp' v hv⟩
    · rintro rfl
      exact hl
  right
  refine ⟨l, lineSingleton, ?_⟩
  apply one_side_incident (fun l p => I p l) L₁ L₂ P₁ P₂
  · intro Y X hy₁ hy₂ hx₁ hx₂
    obtain ⟨p, hp, l, hl, hit⟩ := below X Y hx₁ hx₂ hy₁ hy₂
    exact ⟨l, hl, p, hp, hit⟩
  · exact (Finset.mem_inter.mp hl).1
  · exact (Finset.mem_inter.mp hl).2


lemma row_preserves_edges {α β : Type} [DecidableEq α] [DecidableEq β]
    (P₁ P₂ : Finset α) (L₁ L₂ K : Finset β) (p : α)
    (singleton : P₁ ∩ P₂ = {p}) (existing : K = L₁ ∨ K = L₂) :
    ∀ u v, u ∈ P₁ → u ∈ P₂ → v ∈ L₁ → v ∈ L₂ → u = p ∧ v ∈ K := by
  intro u v hu₁ hu₂ hv₁ hv₂
  constructor
  · apply Finset.mem_singleton.mp
    rw [← singleton]
    exact Finset.mem_inter.mpr ⟨hu₁, hu₂⟩
  · rcases existing with rfl | rfl
    · exact hv₁
    · exact hv₂

end PEqualNP.Outside.L_meta_2583.TwoRectangles
