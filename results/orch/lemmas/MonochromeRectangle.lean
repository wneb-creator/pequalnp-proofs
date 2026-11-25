import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.MonochromeRectangle

lemma clauses_rectangle {α : Type} [Fintype α] [DecidableEq α]
    (color : α → Bool) (clauses : List (Finset α))
    (hmono : ∀ S ∈ clauses,
      (∀ v ∈ S, color v = false) ∨ (∀ v ∈ S, color v = true)) :
    ∃ I J : Finset α, ∀ a b : α, color a = false → color b = true →
      ((∀ S ∈ clauses, a ∈ S ∨ b ∈ S) ↔ a ∈ I ∧ b ∈ J) := by
  classical
  let I := Finset.univ.filter fun a =>
    ∀ S ∈ clauses, (∀ v ∈ S, color v = false) → a ∈ S
  let J := Finset.univ.filter fun b =>
    ∀ S ∈ clauses, (∀ v ∈ S, color v = true) → b ∈ S
  refine ⟨I, J, ?_⟩
  intro a b ha hb
  constructor
  · intro h
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro S hS hcolor
      rcases h S hS with haS | hbS
      · exact haS
      · have hbad := hcolor b hbS
        simp [hb] at hbad
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro S hS hcolor
      rcases h S hS with haS | hbS
      · have hbad := hcolor a haS
        simp [ha] at hbad
      · exact hbS
  · rintro ⟨hI, hJ⟩ S hS
    rcases hmono S hS with hcolor | hcolor
    · exact Or.inl ((Finset.mem_filter.mp hI).2 S hS hcolor)
    · exact Or.inr ((Finset.mem_filter.mp hJ).2 S hS hcolor)

lemma clauses_pair_rectangle {α : Type} [Fintype α] [DecidableEq α]
    (color : α → Bool) (clauses : List (Finset α))
    (hmono : ∀ S ∈ clauses,
      (∀ v ∈ S, color v = false) ∨ (∀ v ∈ S, color v = true)) :
    ∃ I J : Finset α, ∀ a b : α, color a = false → color b = true →
      ((∀ S ∈ clauses, ∃ v ∈ S, v = a ∨ v = b) ↔ a ∈ I ∧ b ∈ J) := by
  obtain ⟨I, J, h⟩ := clauses_rectangle color clauses hmono
  refine ⟨I, J, ?_⟩
  intro a b ha hb
  rw [← h a b ha hb]
  constructor
  · intro hh S hS
    obtain ⟨v, hv, rfl | rfl⟩ := hh S hS
    · exact Or.inl hv
    · exact Or.inr hv
  · intro hh S hS
    rcases hh S hS with haS | hbS
    · exact ⟨a, haS, Or.inl rfl⟩
    · exact ⟨b, hbS, Or.inr rfl⟩

lemma clauses_colored_rectangle {α : Type} [Fintype α] [DecidableEq α]
    (color : α → Bool) (clauses : List (Finset α))
    (hmono : ∀ S ∈ clauses,
      (∀ v ∈ S, color v = false) ∨ (∀ v ∈ S, color v = true)) :
    ∃ I J : Finset α,
      (∀ a ∈ I, color a = false) ∧ (∀ b ∈ J, color b = true) ∧
      ∀ a b : α, color a = false → color b = true →
        ((∀ S ∈ clauses, ∃ v ∈ S, v = a ∨ v = b) ↔ a ∈ I ∧ b ∈ J) := by
  classical
  obtain ⟨I, J, h⟩ := clauses_pair_rectangle color clauses hmono
  refine ⟨I.filter (fun a => color a = false), J.filter (fun b => color b = true),
    (fun a ha => (Finset.mem_filter.mp ha).2),
    (fun b hb => (Finset.mem_filter.mp hb).2), ?_⟩
  intro a b ha hb
  simpa only [Finset.mem_filter, ha, hb, and_true] using h a b ha hb

end PEqualNP.Outside.L_meta_9811.MonochromeRectangle
