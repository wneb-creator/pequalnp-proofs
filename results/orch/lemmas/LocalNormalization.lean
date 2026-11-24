import Mathlib

namespace PEqualNP.Outside.L_meta_3678_aux

lemma matching_intersection (a b c d : Bool) :
    (((a || d) && (b || c)) && ((a || c) && (b || d))) =
      ((a && b) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

lemma matching_first_dirty :
    ∃ a b c d : Bool,
      ((a || d) && (b || c)) = true ∧ ((a && b) || (c && d)) = false := by
  exact ⟨true, false, true, false, rfl, rfl⟩

lemma matching_second_dirty :
    ∃ a b c d : Bool,
      ((a || c) && (b || d)) = true ∧ ((a && b) || (c && d)) = false := by
  exact ⟨true, false, false, true, rfl, rfl⟩

lemma biclique_has_opposite_colors {α : Type*} (s : α → Bool)
    (A B : Set α) (hA : A.Nonempty) (hB : B.Nonempty)
    (h : ∀ a ∈ A, ∀ b ∈ B, s a ≠ s b) :
    ∃ c : Bool, (∀ a ∈ A, s a = c) ∧ (∀ b ∈ B, s b = !c) := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  refine ⟨s a, ?_, ?_⟩
  · intro a' ha'
    have hab := h a ha b hb
    have hab' := h a' ha' b hb
    cases hsa : s a <;> cases hsb : s b <;> cases hsap : s a' <;>
      simp_all
  · intro b' hb'
    have hab' := h a ha b' hb'
    cases hsa : s a <;> cases hsb : s b' <;> simp_all

lemma product_below_graph_iff {α : Type*} (G : SimpleGraph α) (A B : Set α) :
    (∀ x : α → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ↔
    (∀ a ∈ A, ∀ b ∈ B, G.Adj a b) := by
  classical
  constructor
  · intro h a ha b hb
    obtain ⟨u, v, huv, hu, hv⟩ :=
      h (fun w => decide (w = a ∨ w = b))
        ⟨a, ha, by simp⟩ ⟨b, hb, by simp⟩
    simp only [decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (G.loopless.irrefl _ huv)
    · exact huv
    · exact huv.symm
    · exact False.elim (G.loopless.irrefl _ huv)
  · intro h x hx hy
    obtain ⟨a, ha, hxa⟩ := hx
    obtain ⟨b, hb, hxb⟩ := hy
    exact ⟨a, b, h a ha b hb, hxa, hxb⟩

lemma clean_product_has_opposite_colors {α : Type*} (G : SimpleGraph α)
    (s : α → Bool) (hcolor : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B : Set α) (hA : A.Nonempty) (hB : B.Nonempty)
    (hbelow : ∀ x : α → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ c : Bool, (∀ a ∈ A, s a = c) ∧ (∀ b ∈ B, s b = !c) := by
  apply biclique_has_opposite_colors s A B hA hB
  intro a ha b hb
  exact hcolor a b ((product_below_graph_iff G A B).mp hbelow a ha b hb)

end PEqualNP.Outside.L_meta_3678_aux
