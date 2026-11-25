import Mathlib

namespace PEqualNP.Outside.L_meta_2583

lemma incidence_edge_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hcard : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card = N * (q + 1) := by
  classical
  calc
    (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card =
        ∑ e : Fin N × Fin N, if I e.1 e.2 then 1 else 0 := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ l : Fin N, ∑ p : Fin N, if I p l then 1 else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = N * (q + 1) := by simp [hcard]

end PEqualNP.Outside.L_meta_2583
