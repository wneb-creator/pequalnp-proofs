import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.mixedSupport

lemma no_common_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G) (L R : Finset (Fin n)) (a b : Fin n)
    (hab : a ≠ b) (hL : 2 ≤ L.card) (hR : 2 ≤ R.card)
    (ha : ∀ u ∈ L, G.Adj a u) (hb : ∀ u ∈ R, G.Adj b u) :
    ¬ ∃ z : Fin n, ∀ u ∈ L ∪ R, G.Adj z u := by
  rintro ⟨z, hz⟩
  have za : z = a := by
    by_contra hza
    have hsub : L ⊆ Finset.univ.filter (fun u => G.Adj z u ∧ G.Adj a u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz u (Finset.mem_union_left _ hu), ha u hu⟩
    have hc := Finset.card_le_card hsub
    have hd := h4 z a hza
    omega
  have zb : z = b := by
    by_contra hzb
    have hsub : R ⊆ Finset.univ.filter (fun u => G.Adj z u ∧ G.Adj b u) := by
      intro u hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz u (Finset.mem_union_right _ hu), hb u hu⟩
    have hc := Finset.card_le_card hsub
    have hd := h4 z b hzb
    omega
  exact hab (za.symm.trans zb)

end PEqualNP.Outside.L_meta_2448_aux.mixedSupport
