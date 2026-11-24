import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5349

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.MetaComplexity.NestedCover

def singletonSupport (n : ℕ) (C : Circuit) (g : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun v => gateVal n C g (pairInput v v) = true

lemma graphFun_pair_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp, by simp⟩

lemma wmax_singleton_adj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ)
    (hmono : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    {u v : Fin n} (hu : u ∈ wmax G C g) (hv : v ∈ singletonSupport n C g) :
    G.Adj u v := by
  have hvv : gateVal n C g (pairInput v v) = true := (Finset.mem_filter.mp hv).2
  have huv : gateVal n C g (pairInput u v) = true := hmono _ _ (by
    intro w hw
    simp only [pairInput, decide_eq_true_eq] at hw ⊢
    exact Or.inr (hw.elim id id)) hvv
  apply (graphFun_pair_true G u v).mp
  exact (Finset.mem_filter.mp hu).2 _ huv (by simp [pairInput])

lemma singletonSupport_card_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (h4 : NoFourCycle G)
    (hmono : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C g x = true → gateVal n C g y = true)
    {a b : Fin n} (ha : a ∈ wmax G C g) (hb : b ∈ wmax G C g) (hab : a ≠ b) :
    (singletonSupport n C g).card ≤ 1 := by
  have hsub : singletonSupport n C g ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      wmax_singleton_adj G C g hmono ha hv, wmax_singleton_adj G C g hmono hb hv⟩
  exact (Finset.card_le_card hsub).trans (h4 a b hab)

lemma wmax_singleton_card_dichotomy {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (h4 : NoFourCycle G)
    (hmono : ∀ (x y : Fin n → Bool), (∀ v, x v = true → y v = true) →
      gateVal n C g x = true → gateVal n C g y = true) :
    (wmax G C g).card ≤ 1 ∨ (singletonSupport n C g).card ≤ 1 := by
  by_cases hw : (wmax G C g).card ≤ 1
  · exact Or.inl hw
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (Nat.lt_of_not_ge hw)
    exact Or.inr (singletonSupport_card_le_one G C g h4 hmono ha hb hab)

end PEqualNP.Outside.L_meta_5349
