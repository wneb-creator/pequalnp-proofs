import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.UnpairedCell

open PEqualNP.TopForm

def Universal {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ w ∈ S, G.Adj v w

open Classical in
lemma universal_centers_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    (Finset.univ.filter (Universal G S)).card ≤ 1 := by
  classical
  by_contra hlarge
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega :
    1 < (Finset.univ.filter (Universal G S)).card)
  have hsub : S ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Finset.mem_filter.mp ha).2 w hw, (Finset.mem_filter.mp hb).2 w hw⟩
  have h := (Finset.card_le_card hsub).trans (hG a b hab)
  omega

open Classical in
lemma common_active_cell_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hB : 2 ≤ B.card) (hD : 2 ≤ D.card) (hBD : Disjoint B D) :
    ((A ∩ C).filter (fun v =>
      (Universal G B v ∨ ∃ b ∈ B, Universal G A b) ∧
      (Universal G D v ∨ ∃ d ∈ D, Universal G C d))).card ≤ 1 := by
  classical
  let X := (A ∩ C).filter (fun v =>
    (Universal G B v ∨ ∃ b ∈ B, Universal G A b) ∧
    (Universal G D v ∨ ∃ d ∈ D, Universal G C d))
  change X.card ≤ 1
  by_cases hb : ∃ b ∈ B, Universal G A b
  · by_cases hd : ∃ d ∈ D, Universal G C d
    · obtain ⟨b, hbB, hbA⟩ := hb
      obtain ⟨d, hdD, hdC⟩ := hd
      have hbd : b ≠ d := by
        intro he
        exact Finset.disjoint_left.mp hBD hbB (he.symm ▸ hdD)
      have hsub : X ⊆ Finset.univ.filter (fun v => G.Adj b v ∧ G.Adj d v) := by
        intro v hv
        have hAC := Finset.mem_inter.mp (Finset.mem_filter.mp hv).1
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbA v hAC.1, hdC v hAC.2⟩
      exact (Finset.card_le_card hsub).trans (hG b d hbd)
    · have hsub : X ⊆ Finset.univ.filter (Universal G D) := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          (Finset.mem_filter.mp hv).2.2.resolve_right hd⟩
      exact (Finset.card_le_card hsub).trans (universal_centers_small G hG D hD)
  · have hsub : X ⊆ Finset.univ.filter (Universal G B) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (Finset.mem_filter.mp hv).2.1.resolve_right hb⟩
    exact (Finset.card_le_card hsub).trans (universal_centers_small G hG B hB)

end PEqualNP.Outside.L_meta_1477.UnpairedCell
