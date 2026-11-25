import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

lemma incidence_card (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)).card = N * (q + 1) := by
  have hc : ((Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)).card =
      ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [← Finset.univ_product_univ, Finset.sum_product, Finset.sum_comm]
  rw [hc]
  simp [hl]

end PEqualNP.Outside.L_meta_2583_aux
