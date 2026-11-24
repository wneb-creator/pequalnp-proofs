import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.TwoCenters

open PEqualNP.TopForm

lemma cross_edge_centered {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ u ∈ A, G.Adj u b) (hB : ∀ v ∈ B, G.Adj a v)
    (u v : Fin n) (hu : u ∈ A) (hv : v ∈ B) (huv : G.Adj u v) :
    u = a ∨ v = b := by
  by_cases hua : u = a
  · exact Or.inl hua
  apply Or.inr
  by_contra hvb
  have hsub : {b, v} ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj u w) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB _ hb, hA u hu⟩
    · have he : w = v := Finset.mem_singleton.mp hw
      subst w
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB v hv, huv⟩
  have hcard : ({b, v} : Finset (Fin n)).card = 2 := by simp [Ne.symm hvb]
  have hle := (Finset.card_le_card hsub).trans (hG a u (Ne.symm hua))
  omega

lemma cross_edges_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ u ∈ A, G.Adj u b) (hB : ∀ v ∈ B, G.Adj a v) :
    (A ×ˢ B).filter (fun p => G.Adj p.1 p.2) = ({a} ×ˢ B) ∪ (A ×ˢ {b}) := by
  ext p
  rcases p with ⟨u, v⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hu, hv⟩, huv⟩
    rcases cross_edge_centered G hG A B a b ha hb hA hB u v hu hv huv with rfl | rfl
    · exact Or.inl ⟨rfl, hv⟩
    · exact Or.inr ⟨hu, rfl⟩
  · rintro (⟨rfl, hv⟩ | ⟨hu, rfl⟩)
    · exact ⟨⟨ha, hv⟩, hB v hv⟩
    · exact ⟨⟨hu, hb⟩, hA u hu⟩

lemma cross_edges_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B : Finset (Fin n)) (a b : Fin n)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ u ∈ A, G.Adj u b) (hB : ∀ v ∈ B, G.Adj a v) :
    ((A ×ˢ B).filter (fun p => G.Adj p.1 p.2)).card + 1 = A.card + B.card := by
  rw [cross_edges_eq G hG A B a b ha hb hA hB]
  have hi : ({a} ×ˢ B) ∩ (A ×ˢ {b}) = {(a, b)} := by
    ext p
    rcases p with ⟨u, v⟩
    simp only [Finset.mem_inter, Finset.mem_product, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, _⟩, ⟨_, h2⟩⟩
      exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨rfl, hb⟩, ⟨ha, rfl⟩⟩
  have hc := Finset.card_union_add_card_inter ({a} ×ˢ B) (A ×ˢ {b})
  rw [hi] at hc
  simpa [Finset.card_product, Nat.add_comm] using hc

end PEqualNP.Outside.L_meta_1477.TwoCenters
