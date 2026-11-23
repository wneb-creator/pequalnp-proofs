import Mathlib

open Finset

namespace Meta997Aggregation

theorem union_refund {α : Type*} [DecidableEq α]
    (L H R G : Finset α) (hunion : L ∪ H ⊆ G) (hrefund : L ∩ H ⊆ R) :
    L.card + H.card ≤ G.card + R.card := by
  have hu := Finset.card_le_card hunion
  have hi := Finset.card_le_card hrefund
  have he := Finset.card_union_add_card_inter L H
  omega

theorem gate_union_refund {k : ℕ} (L H R : Finset (Fin k))
    (hrefund : L ∩ H ⊆ R) : L.card + H.card ≤ k + R.card := by
  simpa using union_refund L H R Finset.univ (Finset.subset_univ _) hrefund

theorem gate_union_refund_with_spare {k : ℕ} (L H R : Finset (Fin k))
    (hspare : ((L ∩ H) \ R).card ≤ (Finset.univ \ (L ∪ H)).card) :
    L.card + H.card ≤ k + R.card := by
  have hu := Finset.card_sdiff_add_card_eq_card
    (s := L ∪ H) (t := Finset.univ) (Finset.subset_univ _)
  have hi := Finset.card_sdiff_add_card_inter (L ∩ H) R
  have hr : (L ∩ H ∩ R).card ≤ R.card :=
    Finset.card_le_card Finset.inter_subset_right
  have he := Finset.card_union_add_card_inter L H
  simp only [Finset.card_univ, Fintype.card_fin] at hu
  omega

theorem window_aggregation {m k : ℕ} (heavy : Fin m → Prop)
    [DecidablePred heavy] (lightWeight heavyWeight : Fin m → ℕ)
    (L H R : Finset (Fin k))
    (hlight : (∑ i, if heavy i then 0 else lightWeight i - 1) ≤ L.card)
    (hheavy : (∑ i, if heavy i then heavyWeight i - 1 else 0) ≤ H.card)
    (hrefund : L ∩ H ⊆ R) :
    (∑ i, if heavy i then heavyWeight i else lightWeight i) ≤ k + R.card + m := by
  have hp : ∀ i : Fin m,
      (if heavy i then heavyWeight i else lightWeight i) ≤
      (if heavy i then 0 else lightWeight i - 1) +
      (if heavy i then heavyWeight i - 1 else 0) + 1 := by
    intro i
    split <;> simp_all <;> omega
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hs
  have hg := gate_union_refund L H R hrefund
  omega

theorem pairwise_charge_card {m k : ℕ} (A : Fin m → Finset (Fin k))
    (hdisj : ∀ i j, i ≠ j → Disjoint (A i) (A j)) :
    (Finset.univ.biUnion A).card = ∑ i, (A i).card := by
  apply Finset.card_biUnion
  intro i _ j _ hij
  exact hdisj i j hij

theorem family_window_aggregation {m k : ℕ} (heavy : Fin m → Prop)
    [DecidablePred heavy] (lightWeight heavyWeight : Fin m → ℕ)
    (L H : Fin m → Finset (Fin k)) (R : Finset (Fin k))
    (hLdisj : ∀ i j, i ≠ j → Disjoint (L i) (L j))
    (hHdisj : ∀ i j, i ≠ j → Disjoint (H i) (H j))
    (hlight : ∀ i, (if heavy i then 0 else lightWeight i - 1) ≤ (L i).card)
    (hheavy : ∀ i, (if heavy i then heavyWeight i - 1 else 0) ≤ (H i).card)
    (hrefund : (Finset.univ.biUnion L) ∩ (Finset.univ.biUnion H) ⊆ R) :
    (∑ i, if heavy i then heavyWeight i else lightWeight i) ≤ k + R.card + m := by
  apply window_aggregation heavy lightWeight heavyWeight
    (Finset.univ.biUnion L) (Finset.univ.biUnion H) R
  · rw [pairwise_charge_card L hLdisj]
    exact Finset.sum_le_sum fun i _ => hlight i
  · rw [pairwise_charge_card H hHdisj]
    exact Finset.sum_le_sum fun i _ => hheavy i
  · exact hrefund

theorem target_window_aggregation {n m k : ℕ} (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (L H R : Finset (Fin k))
    (hlight : (∑ i, if Disjoint (S i) y then 0 else min y.card (S i).card - 1)
      ≤ L.card)
    (hheavy : (∑ i, if Disjoint (S i) y then (S i).card - 1 else 0) ≤ H.card)
    (hrefund : L ∩ H ⊆ R) :
    (∑ i, if Disjoint (S i) y then (S i).card else min y.card (S i).card)
      ≤ k + R.card + m := by
  exact window_aggregation (fun i => Disjoint (S i) y)
    (fun i => min y.card (S i).card) (fun i => (S i).card) L H R
    hlight hheavy hrefund

end Meta997Aggregation
