import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.FlagBudget

open PEqualNP.TopForm

lemma off_centre_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (Q : Finset (Fin n)) (z : Fin n)
    (hQ : ∀ q ∈ Q, G.Adj z q) {p q q' : Fin n}
    (hpz : p ≠ z) (hq : q ∈ Q) (hq' : q' ∈ Q)
    (hpq : G.Adj p q) (hpq' : G.Adj p q') : q = q' := by
  apply Finset.card_le_one.mp (h4 p z hpz)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpq, hQ q hq⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hpq', hQ q' hq'⟩

lemma off_centre_edge_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q : Finset (Fin n)) (z : Fin n)
    (hQ : ∀ q ∈ Q, G.Adj z q) :
    (((P.erase z) ×ˢ Q).filter fun pq => G.Adj pq.1 pq.2).card ≤ (P.erase z).card := by
  let R := ((P.erase z) ×ˢ Q).filter fun pq => G.Adj pq.1 pq.2
  have hinj : Set.InjOn Prod.fst (↑R : Set (Fin n × Fin n)) := by
    intro a ha b hb hab
    change a ∈ R at ha
    change b ∈ R at hb
    obtain ⟨haProd, haG⟩ := Finset.mem_filter.mp ha
    obtain ⟨haP, haQ⟩ := Finset.mem_product.mp haProd
    obtain ⟨hbProd, hbG⟩ := Finset.mem_filter.mp hb
    obtain ⟨hbP, hbQ⟩ := Finset.mem_product.mp hbProd
    apply Prod.ext hab
    apply off_centre_unique G h4 Q z hQ (Finset.mem_erase.mp haP).1 haQ hbQ haG
    simpa only [hab] using hbG
  have hsub : R.image Prod.fst ⊆ P.erase z := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp ha).1).1
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

lemma one_centre_product_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (P Q : Finset (Fin n)) (z : Fin n)
    (hQ : ∀ q ∈ Q, G.Adj z q) :
    ((P ×ˢ Q).filter fun pq => G.Adj pq.1 pq.2).card ≤
      (P.erase z).card + Q.card := by
  let R := (P ×ˢ Q).filter fun pq => G.Adj pq.1 pq.2
  let Roff := ((P.erase z) ×ˢ Q).filter fun pq => G.Adj pq.1 pq.2
  have hsub : R ⊆ Roff ∪ ({z} ×ˢ Q) := by
    intro a ha
    obtain ⟨haP, haQ, haG⟩ := by
      simpa only [R, Finset.mem_filter, Finset.mem_product, and_assoc] using ha
    by_cases haz : a.1 = z
    · apply Finset.mem_union_right
      exact Finset.mem_product.mpr ⟨by simpa only [Finset.mem_singleton] using haz, haQ⟩
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_erase.mpr ⟨haz, haP⟩, haQ⟩, haG⟩
  calc
    R.card ≤ (Roff ∪ ({z} ×ˢ Q)).card := Finset.card_le_card hsub
    _ ≤ Roff.card + ({z} ×ˢ Q).card := Finset.card_union_le _ _
    _ ≤ (P.erase z).card + Q.card := by
      simpa only [Finset.card_product, Finset.card_singleton, one_mul] using
        Nat.add_le_add_right (off_centre_edge_budget G h4 P Q z hQ) (({z} ×ˢ Q).card)

end PEqualNP.Outside.L_meta_5012.FlagBudget
