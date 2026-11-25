import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_2583

lemma perfect_matching_cover_card {N : Nat} (I : Fin N → Fin N → Prop)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ p, I p (σ p))
    (S T : Finset (Fin N))
    (cover : ∀ p l, I p l → p ∈ S ∨ l ∈ T) : N ≤ S.card + T.card := by
  have hcover : Finset.univ ⊆ S ∪ T.map σ.symm.toEmbedding := by
    intro p hp
    rcases cover p (σ p) (hσ p) with hs | ht
    · exact Finset.mem_union.mpr (Or.inl hs)
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_map.mpr ⟨σ p, ht, σ.symm_apply_apply p⟩
  have hc := Finset.card_le_card hcover
  have hu := Finset.card_union_le S (T.map σ.symm.toEmbedding)
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_map] at hc hu
  exact hc.trans hu

lemma small_opposite_neighborhoods_not_cover {q N : Nat}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ p, I p (σ p))
    (p l : Fin N)
    (hl : (Finset.univ.filter (fun a => I a l)).card ≤ q + 1)
    (hp : (Finset.univ.filter (fun b => I p b)).card ≤ q + 1)
    (S T : Finset (Fin N))
    (hS : ∀ s ∈ S, I s l) (hT : ∀ t ∈ T, I p t) :
    ¬ (∀ a b, I a b → a ∈ S ∨ b ∈ T) := by
  intro cover
  have hs : S.card ≤ q + 1 := by
    apply le_trans (Finset.card_le_card ?_) hl
    intro s hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, hS s hs⟩
  have ht : T.card ≤ q + 1 := by
    apply le_trans (Finset.card_le_card ?_) hp
    intro t ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ t, hT t ht⟩
  have hc := perfect_matching_cover_card I σ hσ S T cover
  have hmul : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  rw [pow_two] at hN
  omega

lemma one_extra_edge_filter_constraints {N : Nat}
    (I : Fin N → Fin N → Prop) (p l : Fin N) (nonincident : ¬ I p l)
    (S T : Finset (Fin N))
    (repair : ∀ X Y : Finset (Fin N),
      (((∃ a ∈ X, ∃ b ∈ Y, I a b) ∨ (p ∈ X ∧ l ∈ Y)) ∧
        ((X ∩ S).Nonempty ∨ (Y ∩ T).Nonempty)) ↔
      (∃ a ∈ X, ∃ b ∈ Y, I a b)) :
    (∀ a b, I a b → a ∈ S ∨ b ∈ T) ∧
    (∀ s ∈ S, I s l) ∧ (∀ t ∈ T, I p t) := by
  constructor
  · intro a b hab
    have h := (repair {a} {b}).mpr ⟨a, by simp, b, by simp, hab⟩
    rcases h.2 with ⟨w, hw⟩ | ⟨w, hw⟩
    · have hw' := Finset.mem_inter.mp hw
      have he : w = a := Finset.mem_singleton.mp hw'.1
      exact Or.inl (he ▸ hw'.2)
    · have hw' := Finset.mem_inter.mp hw
      have he : w = b := Finset.mem_singleton.mp hw'.1
      exact Or.inr (he ▸ hw'.2)
  · constructor
    · intro s hs
      have h := (repair {p, s} {l}).mp
        ⟨Or.inr ⟨by simp, by simp⟩,
          Or.inl ⟨s, Finset.mem_inter.mpr ⟨by simp, hs⟩⟩⟩
      simpa [nonincident] using h
    · intro t ht
      have h := (repair {p} {l, t}).mp
        ⟨Or.inr ⟨by simp, by simp⟩,
          Or.inr ⟨t, Finset.mem_inter.mpr ⟨by simp, ht⟩⟩⟩
      simpa [nonincident] using h

lemma one_extra_edge_linear_filter_impossible {q N : Nat}
    (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (σ : Equiv.Perm (Fin N)) (hσ : ∀ p, I p (σ p))
    (p l : Fin N) (nonincident : ¬ I p l)
    (hl : (Finset.univ.filter (fun a => I a l)).card ≤ q + 1)
    (hp : (Finset.univ.filter (fun b => I p b)).card ≤ q + 1)
    (S T : Finset (Fin N)) :
    ¬ (∀ X Y : Finset (Fin N),
      (((∃ a ∈ X, ∃ b ∈ Y, I a b) ∨ (p ∈ X ∧ l ∈ Y)) ∧
        ((X ∩ S).Nonempty ∨ (Y ∩ T).Nonempty)) ↔
      (∃ a ∈ X, ∃ b ∈ Y, I a b)) := by
  intro repair
  obtain ⟨cover, hs, ht⟩ := one_extra_edge_filter_constraints I p l nonincident S T repair
  exact small_opposite_neighborhoods_not_cover I hq hN σ hσ p l hl hp S T hs ht cover

end PEqualNP.Outside.L_meta_2583
