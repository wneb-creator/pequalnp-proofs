import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_951

lemma private_erasure_demand {n m : ℕ} (S : Fin m → Finset (Fin n))
    (i : Fin m) (v : Fin n) (hv : v ∈ S i) (hsize : 2 ≤ (S i).card)
    (hprivate : ∀ j, j ≠ i → v ∉ S j) :
    (∑ j : Fin m, (((S j).erase v).card - 1)) + 1 =
      ∑ j : Fin m, ((S j).card - 1) := by
  have hpoint (j : Fin m) :
      (((S j).erase v).card - 1) + (if j = i then 1 else 0) = (S j).card - 1 := by
    by_cases hji : j = i
    · subst j
      rw [Finset.card_erase_of_mem hv]
      simp only [ite_true]
      omega
    · rw [Finset.erase_eq_of_notMem (hprivate j hji)]
      simp [hji]
  have hh := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun j _ => hpoint j)
  simpa only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hh

lemma erased_family_linear {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hlin : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) (v : Fin n) :
    ∀ i j, i ≠ j → ((S i).erase v ∩ (S j).erase v).card ≤ 1 := by
  intro i j hij
  apply le_trans (Finset.card_le_card (Finset.inter_subset_inter
    (Finset.erase_subset v (S i)) (Finset.erase_subset v (S j))))
  exact hlin i j hij

end PEqualNP.Outside.L_meta_951
