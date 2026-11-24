import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.UnpairedCell

open PEqualNP.TopForm

def Universal {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (v : Fin n) : Prop :=
  ∀ w ∈ S, G.Adj v w

open Classical in
lemma common_active_cell_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n))
    (hB : B.Nonempty) (hD : D.Nonempty) (hBD : Disjoint B D) :
    ((A ∩ C).filter (fun v =>
      (Universal G B v ∨ ∃ b ∈ B, Universal G A b) ∧
      (Universal G D v ∨ ∃ d ∈ D, Universal G C d))).card ≤ 1 := by
  classical
  let X := (A ∩ C).filter (fun v =>
    (Universal G B v ∨ ∃ b ∈ B, Universal G A b) ∧
    (Universal G D v ∨ ∃ d ∈ D, Universal G C d))
  change X.card ≤ 1
  have left_center : ∃ b ∈ B, ∀ v ∈ X, G.Adj b v := by
    by_cases hb : ∃ b ∈ B, Universal G A b
    · obtain ⟨b, hbB, hbA⟩ := hb
      exact ⟨b, hbB, fun v hv => hbA v (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).1⟩
    · obtain ⟨b, hbB⟩ := hB
      refine ⟨b, hbB, ?_⟩
      intro v hv
      exact (((Finset.mem_filter.mp hv).2.1.resolve_right hb) b hbB).symm
  have right_center : ∃ d ∈ D, ∀ v ∈ X, G.Adj d v := by
    by_cases hd : ∃ d ∈ D, Universal G C d
    · obtain ⟨d, hdD, hdC⟩ := hd
      exact ⟨d, hdD, fun v hv => hdC v (Finset.mem_inter.mp (Finset.mem_filter.mp hv).1).2⟩
    · obtain ⟨d, hdD⟩ := hD
      refine ⟨d, hdD, ?_⟩
      intro v hv
      exact (((Finset.mem_filter.mp hv).2.2.resolve_right hd) d hdD).symm
  obtain ⟨b, hbB, hbX⟩ := left_center
  obtain ⟨d, hdD, hdX⟩ := right_center
  have hbd : b ≠ d := by
    intro he
    exact Finset.disjoint_left.mp hBD hbB (he.symm ▸ hdD)
  have hsub : X ⊆ Finset.univ.filter (fun v => G.Adj b v ∧ G.Adj d v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbX v hv, hdX v hv⟩
  exact (Finset.card_le_card hsub).trans (hG b d hbd)

end PEqualNP.Outside.L_meta_1477.UnpairedCell
