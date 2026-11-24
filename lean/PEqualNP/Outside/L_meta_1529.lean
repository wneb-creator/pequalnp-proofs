import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1529

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) := by
  intro n G _ hG P Q W hW
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw hwP
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwQ
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro q hq
      rcases h w hwP q hq with h1 | h1 | h1
      · exact h1
      · exact absurd h1 G.irrefl
      · exact h1.symm
  · intro w hw hwQ
    have h := (hW w).1 hw
    refine ⟨?_, ?_⟩
    · intro hwP
      rcases h w hwP w hwQ with h1 | h1 | h1 <;> exact G.irrefl h1
    · intro p hp
      rcases h p hp w hwQ with h1 | h1 | h1
      · exact h1.symm
      · exact h1.symm
      · exact absurd h1 G.irrefl
  · intro s hs w hw
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW w).1 hw s hsP s hsQ with h1 | h1 | h1
    · exact absurd h1 G.irrefl
    · exact h1
    · exact h1
  · intro s hs hsW
    have hsP := (Finset.mem_inter.1 hs).1
    have hsQ := (Finset.mem_inter.1 hs).2
    rcases (hW s).1 hsW s hsP s hsQ with h1 | h1 | h1 <;> exact G.irrefl h1
  · intro h2
    obtain ⟨s, hs, t, ht, hst⟩ := Finset.one_lt_card.1 h2
    have key : ∀ u ∈ P ∩ Q, ∀ w ∈ W, G.Adj u w := by
      intro u hu w hw
      have huP := (Finset.mem_inter.1 hu).1
      have huQ := (Finset.mem_inter.1 hu).2
      rcases (hW w).1 hw u huP u huQ with h1 | h1 | h1
      · exact absurd h1 G.irrefl
      · exact h1
      · exact h1
    refine le_trans (Finset.card_le_card ?_) (hG s t hst)
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨key s hs w hw, key t ht w hw⟩

end PEqualNP.Outside.L_meta_1529

theorem PEqualNP.Outside.L_meta_1529 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (∀ w ∈ W, w ∈ P → w ∉ Q ∧ ∀ q ∈ Q, G.Adj w q) ∧
    (∀ w ∈ W, w ∈ Q → w ∉ P ∧ ∀ p ∈ P, G.Adj w p) ∧
    (∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w) ∧ (∀ s ∈ P ∩ Q, s ∉ W) ∧
    (2 ≤ (P ∩ Q).card → W.card ≤ 1) :=
  PEqualNP.Outside.L_meta_1529.main_aux
