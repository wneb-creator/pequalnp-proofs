import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.MixedShared
open PEqualNP.TopForm

lemma common_filter_forces_centers {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q)
    (hpU : p ∈ U) (hpV : p ∈ V) (hqU : q ∈ U) (hqV : q ∈ V) :
    ∀ a ∈ P, ∀ b ∈ Q, (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) →
      a = p ∨ b = q := by
  classical
  intro a ha b hb hU hV
  by_cases hap : a = p
  · exact Or.inl hap
  apply Or.inr
  have hs := Finset.card_le_one.mp (hG a p hap)
  apply hs
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcross a ha b hb hU hV,
      hcross p hp b hb (Or.inl hpU) (Or.inl hpV)⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a ha q hq (Or.inr hqU) (Or.inr hqV),
      hcross p hp q hq (Or.inl hpU) (Or.inl hpV)⟩

lemma common_filter_cover_two {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (p q : Fin n) (hp : p ∈ P) (hq : q ∈ Q)
    (hpU : p ∈ U) (hpV : p ∈ V) (hqU : q ∈ U) (hqV : q ∈ V) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ G.Adj p q ∧
      ∀ a ∈ P, ∀ b ∈ Q, (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) →
        a ∈ T ∨ b ∈ T := by
  classical
  refine ⟨{p, q}, by simpa using (Finset.card_insert_le p ({q} : Finset (Fin n))),
    hcross p hp q hq (Or.inl hpU) (Or.inl hpV), ?_⟩
  intro a ha b hb hU hV
  rcases common_filter_forces_centers G hG P Q U V hcross p q hp hq hpU hpV hqU hqV
    a ha b hb hU hV with rfl | rfl
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

lemma two_common_left_force_right_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (hP : 2 ≤ (P.filter fun p => p ∈ U ∧ p ∈ V).card) : Q.card ≤ 1 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (P.filter fun p => p ∈ U ∧ p ∈ V).card)
  obtain ⟨haP, haU, haV⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbP, hbU, hbV⟩ := Finset.mem_filter.mp hb
  have hsub : Q ⊆ Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q) := by
    intro q hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      hcross a haP q hq (Or.inl haU) (Or.inl haV),
      hcross b hbP q hq (Or.inl hbU) (Or.inl hbV)⟩
  exact (Finset.card_le_card hsub).trans (hG a b hab)

lemma two_common_right_force_left_small {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG : NoFourCycle G) (P Q U V : Finset (Fin n))
    (hcross : ∀ a ∈ P, ∀ b ∈ Q,
      (a ∈ U ∨ b ∈ U) → (a ∈ V ∨ b ∈ V) → G.Adj a b)
    (hQ : 2 ≤ (Q.filter fun q => q ∈ U ∧ q ∈ V).card) : P.card ≤ 1 :=
  two_common_left_force_right_small G hG Q P U V
    (fun a ha b hb hU hV => (hcross b hb a ha hU.symm hV.symm).symm) hQ

end PEqualNP.Outside.L_meta_1477.MixedShared
