import UpstreamGraph

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projected_exclude63 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 63=ineligSet 14 D) : 12≤Bplus 14 D := by
  classical
  have sub : wide (mask 16000) ⊆ mask 63 := by decide +kernel
  have marked : marks D (mask 16000) = wide (mask 16000) := by
    apply Finset.Subset.antisymm (Finset.filter_subset _ _)
    intro i hi
    apply mark_iff.mpr
    exact ⟨by simpa [wide] using hi,
      occurs h hc z (mask 16000) (by decide +kernel) i (eq ▸ sub hi)⟩
  have bound := projected_count h hc (mask 16000) (by decide +kernel) (by decide +kernel)
  rw [marked, ←eq] at bound
  have size := inelig_card_add 14 D
  rw [←eq] at size
  have card : (mask 63).card=6 ∧ (mask 16000).card=6 ∧
      (wide (mask 16000)).card=4 ∧ (mask 63 ∩ wide (mask 16000)).card=4 ∧
      (labels (mask 16000) (wide (mask 16000))).card=4 := by decide +kernel
  have inter := Finset.card_le_card (Finset.inter_subset_left :
    mask 16000 ∩ eligSet 14 D ⊆ mask 16000)
  omega

end PEqualNP.Outside.L_meta_9775.UpstreamCore
