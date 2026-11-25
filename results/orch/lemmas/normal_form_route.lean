import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma normal_biclique_thin {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (noFour : NoFourCycle G) (A B : Finset (Fin n))
    (cross : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  classical
  by_cases small : A.card ≤ 1
  · exact Or.inl small
  right
  obtain ⟨a, ha, b, hb, different⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  have sub : B ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cross a ha w hw, cross b hb w hw⟩
  exact (Finset.card_le_card sub).trans (noFour a b different)

lemma normal_graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  simp only [Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨a, b, adjacent, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl adjacent).elim
    · exact adjacent
    · exact adjacent.symm
    · exact (G.irrefl adjacent).elim
  · intro adjacent
    exact ⟨u, v, adjacent, by simp [pairInput], by simp [pairInput]⟩

lemma normal_product_below_thin {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (noFour : NoFourCycle G) (A B : Finset (Fin n))
    (below : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) → graphFun G ∅ x = true) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  apply normal_biclique_thin G noFour A B
  intro a ha b hb
  apply (normal_graph_pair G a b).mp
  exact below (pairInput a b) ⟨a, ha, by simp [pairInput]⟩
    ⟨b, hb, by simp [pairInput]⟩

end PEqualNP.Outside.L_meta_1772_aux
