import RemainingI1Audit
import R0CurrentAdapterAudit

namespace PEqualNP.Outside.L_meta_2590_aux.I1Canonical

open DagTools

def zeroPerm (v : Fin 10) : Fin 120 := ![0, 7, 24, 1, 28, 25, 42, 4, 6, 8] v

lemma selected_zero (v : Fin 10) : I0Proof.Petersen.permV (zeroPerm v) v = 0 := by
  fin_cases v <;> decide +kernel

lemma equiv_zero (v : Fin 10) : I0Proof.Petersen.permEquiv (zeroPerm v) v = 0 := by
  change I0Proof.Petersen.permV (zeroPerm v) v = 0
  exact selected_zero v

lemma perm_adj (k : Fin 120) (u v : Fin 10) :
    DeskDriver.adj (I0Proof.Petersen.permEquiv k u) (I0Proof.Petersen.permEquiv k v) ↔
      DeskDriver.adj u v := by
  simpa only [FoundationI0.graph_agreement] using
    I0Proof.DagTools.I0Case.permutation_adj k u v

lemma singleton_to_zero {D : Dag} (h : StrictLive 10 D)
    (hc : sem_Comp 10 DeskDriver.adj D) (hi : (ineligSet 10 D).card = 1) :
    ∃ E : Dag, StrictLive 10 E ∧ sem_Comp 10 DeskDriver.adj E ∧
      E.length = D.length ∧ ineligSet 10 E = ({0} : Finset (Fin 10)) := by
  classical
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hi
  let σ := I0Proof.Petersen.permEquiv (zeroPerm v)
  refine ⟨relabel σ D, relabel_strictLive σ h,
    I0Proof.DagTools.relabel_comp σ h hc (perm_adj (zeroPerm v)),
    relabel_length σ D, ?_⟩
  rw [relabel_ineligSet σ h.1, hv, Finset.image_singleton]
  change ({I0Proof.Petersen.permEquiv (zeroPerm v) v} : Finset (Fin 10)) = {0}
  rw [equiv_zero]

end PEqualNP.Outside.L_meta_2590_aux.I1Canonical

namespace PEqualNP.Outside.L_meta_2590_aux.ActualThreeProfiles

open DagTools PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 12000 in
lemma r1_graph_iff : ∀ u v,
    DeskDriver.adj u v ↔ R1Standalone.DagTools.petersenAdj u v := by
  unfold DeskDriver.adj R1Standalone.DagTools.petersenAdj
  decide +kernel

lemma r1_graph_agreement : DeskDriver.adj = R1Standalone.DagTools.petersenAdj := by
  funext u v
  exact propext (r1_graph_iff u v)

set_option maxRecDepth 12000 in
lemma circuit_three_profiles (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 19)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = DeskDriver.target x) :
    ∃ E : Dag, StrictLive 10 E ∧ sem_Comp 10 DeskDriver.adj E ∧ E.length ≤ 19 ∧
      (0 : Fin 10) ∈ ineligSet 10 E ∧ Bzero 10 E = 0 ∧
      Bplus 10 E = (eligSet 10 E).card + 1 ∧
      (R1Standalone.DagTools.h3_saturatedSet 10 E = {1,4} ∨
       R1Standalone.DagTools.h3_saturatedSet 10 E = {1,4,5} ∨
       R1Standalone.DagTools.h3_saturatedSet 10 E = {3,6,7}) := by
  obtain ⟨D, hD, hcD, hlenD, hiD⟩ := RemainingI1.circuit_remaining_one C hm hs hf
  obtain ⟨D0, hD0, hcD0, hlen0, hI0⟩ := I1Canonical.singleton_to_zero hD hcD hiD
  have hz0 : (0 : Fin 10) ∈ ineligSet 10 D0 := by rw [hI0]; simp
  have hi0 : (ineligSet 10 D0).card = 1 := by rw [hI0]; simp
  have hs0 : D0.length ≤ 19 := by omega
  have hcR : R1Standalone.DagTools.sem_Comp 10 R1Standalone.DagTools.petersenAdj D0 := by
    change sem_Comp 10 R1Standalone.DagTools.petersenAdj D0
    simpa only [← r1_graph_agreement] using hcD0
  obtain ⟨E, hE, hcE, hzE, hB0, hBplus, hlenE, hprofiles⟩ :=
    R1Standalone.DagTools.h3_actual_i1_reduction_three hD0 hcR hz0 hi0 hs0
  refine ⟨E, hE, ?_, ?_, hzE, hB0, hBplus, hprofiles⟩
  · change sem_Comp 10 R1Standalone.DagTools.petersenAdj E at hcE
    simpa only [← r1_graph_agreement] using hcE
  · omega

end PEqualNP.Outside.L_meta_2590_aux.ActualThreeProfiles
