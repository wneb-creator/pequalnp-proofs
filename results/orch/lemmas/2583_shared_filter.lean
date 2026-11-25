import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_2583

lemma three_incident_corners_exclude_fourth {N : Nat}
    (I : Fin N → Fin N → Prop)
    (uniqueLine : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hp : p ≠ p') (hl : l ≠ l')
    (hpl : I p l) (hpl' : I p l') (hp'l : I p' l) : ¬ I p' l' := by
  intro hp'l'
  obtain ⟨w, hw, hu⟩ := uniqueLine p p' hp
  exact hl ((hu l ⟨hpl, hp'l⟩).trans (hu l' ⟨hpl', hp'l'⟩).symm)

lemma opposite_neighborhood_edges_card {N : Nat}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (uniqueLine : ∀ p p', p ≠ p' → ∃! l, I p l ∧ I p' l)
    (p l : Fin N) (nonincident : ¬ I p l)
    (S T : Finset (Fin N))
    (hS : ∀ s ∈ S, I s l) (hT : ∀ t ∈ T, I p t) :
    ((S ×ˢ T).filter fun e => I e.1 e.2).card ≤ min S.card T.card := by
  have rows : ∀ a ∈ S, ∀ b ∈ T, ∀ c ∈ T, I a b → I a c → b = c := by
    intro a ha b hb c hc hab hac
    have hap : a ≠ p := by
      intro he
      subst a
      exact nonincident (hS p ha)
    obtain ⟨w, hw, hu⟩ := uniqueLine a p hap
    exact (hu b ⟨hab, hT b hb⟩).trans (hu c ⟨hac, hT c hc⟩).symm
  have cols : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ T, I a c → I b c → a = b := by
    intro a ha b hb c hc hac hbc
    by_contra hab
    obtain ⟨w, hw, hu⟩ := uniqueLine a b hab
    have hcl : c = l := (hu c ⟨hac, hbc⟩).trans (hu l ⟨hS a ha, hS b hb⟩).symm
    exact nonincident (hcl ▸ hT c hc)
  apply le_min
  · apply Finset.card_le_card_of_injOn Prod.fst
    · intro e he
      exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    · intro e he f hf heq
      rcases e with ⟨a, b⟩
      rcases f with ⟨c, d⟩
      dsimp at heq
      subst c
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at he hf
      exact Prod.ext rfl (rows a he.1.1 b he.1.2 d hf.1.2 he.2 hf.2)
  · apply Finset.card_le_card_of_injOn Prod.snd
    · intro e he
      exact (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
    · intro e he f hf heq
      rcases e with ⟨a, b⟩
      rcases f with ⟨c, d⟩
      dsimp at heq
      subst d
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at he hf
      exact Prod.ext (cols a he.1.1 c hf.1.1 b he.1.2 he.2 hf.2) rfl

end PEqualNP.Outside.L_meta_2583
