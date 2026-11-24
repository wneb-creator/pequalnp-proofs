import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.StructuralIsolation

lemma common_neighbor_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (B : Finset (Fin n)) (hB : 2 ≤ B.card)
    (a c : Fin n) (ha : ∀ b ∈ B, G.Adj a b) (hc : ∀ b ∈ B, G.Adj c b) : a = c := by
  by_contra hac
  have hsub : B ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
    intro b hb
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha b hb, hc b hb⟩
  have hsmall := (Finset.card_le_card hsub).trans (h4 a c hac)
  omega

lemma augmented_star_has_no_mask {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (B : Finset (Fin n)) (hB : 2 ≤ B.card)
    (a z : Fin n) (ha : ∀ b ∈ B, G.Adj a b) (haz : ¬ G.Adj a z) :
    ¬ ∃ c : Fin n, ∀ b ∈ insert z B, G.Adj c b := by
  rintro ⟨c, hc⟩
  have hac := common_neighbor_unique G h4 B hB a c ha
    (fun b hb => hc b (Finset.mem_insert_of_mem hb))
  subst c
  exact haz (hc z (Finset.mem_insert_self _ _))

lemma different_sides_no_mask {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (a b : Fin n) (hab : side a ≠ side b) :
    ¬ ∃ c : Fin n, G.Adj c a ∧ G.Adj c b := by
  rintro ⟨c, hca, hcb⟩
  have h1 := hbip c a hca
  have h2 := hbip c b hcb
  cases ha : side a <;> cases hb : side b <;> cases hc : side c <;> simp_all

lemma masked_support_no_other_input {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool) (hbip : ∀ u v, G.Adj u v → side u ≠ side v)
    (S T : Finset (Fin n)) (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S)
    (hab : side a ≠ side b) (hcross : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t) : T = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  exact different_sides_no_mask G side hbip a b hab
    ⟨t, (hcross a ha t ht).symm, (hcross b hb t ht).symm⟩

end PEqualNP.Outside.L_meta_1477.StructuralIsolation
