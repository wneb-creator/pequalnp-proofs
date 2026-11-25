import UpstreamGraph

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

theorem relabel_support_surplus {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) (b : Bool) :
    surplusOn (relabel σ D) ((inner n (relabel σ D)).filter
      (fun w => decide ((supp n (relabel σ D) w).Nonempty) = b)) =
    surplusOn D ((inner n D).filter (fun w => decide ((supp n D w).Nonempty) = b)) := by
  have hlen := List.length_pos_iff.mpr h.2.2
  have mem (w : Nat) :
      liftP σ w ∈ (inner n (relabel σ D)).filter
          (fun v => decide ((supp n (relabel σ D) v).Nonempty) = b) ↔
      w ∈ (inner n D).filter (fun v => decide ((supp n D v).Nonempty) = b) := by
    simp only [Finset.mem_filter, inner, Finset.mem_range, relabel_length,
      relabel_supp σ h.1, Finset.image_nonempty]
    rw [tr_liftP_lt_iff σ (by omega)]
  unfold surplusOn
  symm
  refine Finset.sum_bij (fun w _ => liftP σ w) ?_ ?_ ?_ ?_
  · intro w hw
    exact (mem w).mpr hw
  · intro a ha c hc eq
    exact (tr_liftP_inj σ).mp eq
  · intro w hw
    refine ⟨liftP σ⁻¹ w, ?_, tr_liftP_inv' σ w⟩
    apply (mem _).mp
    simpa only [tr_liftP_inv'] using hw
  · intro w hw
    rw [relabel_fanout]

theorem relabel_Bplus {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) : Bplus n (relabel σ D) = Bplus n D := by
  simpa only [decide_eq_true_eq, Bplus] using relabel_support_surplus σ h true

theorem relabel_Bzero {n : Nat} (σ : Equiv.Perm (Fin n)) {D : Dag}
    (h : StrictLive n D) : Bzero n (relabel σ D) = Bzero n D := by
  simpa only [decide_eq_false_iff_not, Bzero] using relabel_support_surplus σ h false

end PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools
