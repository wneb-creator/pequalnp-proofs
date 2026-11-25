import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.ProductiveStep

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.Outside.L_meta_4675.Pruning PEqualNP.Outside.L_meta_4675.PruningPrefix
  PEqualNP.Outside.L_meta_4675.PruningTrace PEqualNP.Outside.L_meta_4675.StarAppendOptional
  PEqualNP.Outside.L_meta_4675.PruneRestore PEqualNP.Outside.L_meta_4675.LiftMeasure

lemma cone_has_direct_reader (n : ℕ) (C : Circuit) (q : ℕ) :
    ∀ r, r < C.gates.length → InCone n C q r →
      ∃ s < C.gates.length, q < s ∧ n + q ∈ (gateAt C s).inputs := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro hr hc
    unfold InCone at hc
    rw [PEqualNP.Outside.L_meta_4675.OneJunk.cones_getD_eq n C r hr, List.mem_flatMap] at hc
    obtain ⟨w, hw, hc⟩ := hc
    simp only [List.mem_filter, decide_eq_true_eq] at hw
    simp only [List.mem_cons] at hc
    rcases hc with he | hc
    · refine ⟨r, hr, by omega, ?_⟩
      have hwe : n + q = w := by omega
      rw [hwe]
      exact hw.1
    · exact ih (w - n) (by omega) (by omega) hc

lemma graph_singleton_false (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (i : Fin n) : graphFun G ∅ (fun k => decide (k = i)) = false := by
  simp [graphFun]

lemma improve (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (colour : ℕ → Bool) (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hz : tCount n C colour = 0)
    (hnot : ¬ TopForm G C) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      tCount n D colour = 0 ∧ D.size ≤ C.size ∧ andPairs n D < andPairs n C := by
  classical
  unfold TopForm at hnot
  push Not at hnot
  obtain ⟨q, hq, r, hr, hqand, hbelow, hrand, hcone⟩ := hnot
  obtain ⟨s, hs, hqs, hread⟩ := cone_has_direct_reader n C q r hr hcone
  have hread' : n + q ∈ C.gates[s].inputs := by
    rwa [PEqualNP.Outside.L_meta_4675.PruningTrace.gateAt_eq_getElem C s hs] at hread
  have hm : gateAt C q ∈ C.gates := by
    rw [PEqualNP.Outside.L_meta_4675.PruningTrace.gateAt_eq_getElem C q hq]
    exact List.getElem_mem hq
  obtain ⟨a, b, hinputs⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have ha : a < n + q := hAO.2.1 q hq a (by simp [hinputs])
  have hb : b < n + q := hAO.2.1 q hq b (by simp [hinputs])
  have hprod : PEqualNP.CircuitMoves.WireBelowOutput n C (n + q) := by
    intro x hx
    change circuitFun n C x = true
    rw [hfun]
    exact hbelow x hx
  have hsemantic : ∀ x : Fin n → Bool,
      graphFun G ∅ x = ((forcedValues n q C (List.ofFn x)).getD C.output false ||
        ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false)) := by
    intro x
    have he := productive_lift_input n q C hprod x
    rw [hfun] at he
    have hg : PEqualNP.BlindGate.wireValue C n x (n + q) =
        ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false) := by
      rw [PEqualNP.Outside.L_meta_4675.MaskingNext.wireValue_gate n C x q hq hAO.2.1,
        hqand, hinputs]
      simp [GateOp.eval, PEqualNP.BlindGate.wireValue]
    rwa [hg] at he
  have hAP := pruned_ao n q C hAO
  have hap := prior_wire_valid n q C hAO (by omega) a ha
  have hbp := prior_wire_valid n q C hAO (by omega) b hb
  have hreach : orIn n (pruned n q C) (pruned n q C).output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    let x : Fin n → Bool := fun k => decide (k = i)
    have hv := PEqualNP.Outside.L_meta_4675.MaskingNext.orIn_true n (pruned n q C)
      hAP x (pruned n q C).output i hi (by simp [x])
    change (pruned n q C).eval (List.ofFn x) = true at hv
    have he := hsemantic x
    rw [← pruned_eval n q C hAO (List.ofFn x) (by simp), hv] at he
    have hf : graphFun G ∅ x = false := graph_singleton_false n G i
    rw [hf] at he
    simp at he
  let D := restoreStar n (pruned n q C) a b
  refine ⟨D, restoreStar_ao n _ a b hAP hap hbp, ?_, ?_, ?_, ?_⟩
  · funext x
    change (restoreStar n (pruned n q C) a b).eval (List.ofFn x) = graphFun G ∅ x
    rw [restoreStar_eval n _ a b (List.ofFn x) (by simp),
      pruned_eval n q C hAO (List.ofFn x) (by simp),
      pruned_wire_before n q C hAO (by omega) (List.ofFn x) (by simp) a ha,
      pruned_wire_before n q C hAO (by omega) (List.ofFn x) (by simp) b hb]
    exact (hsemantic x).symm
  · change tCount n (restoreStar n (pruned n q C) a b) colour = 0
    rw [restoreStar_tCount n _ a b colour hAP hap hbp hreach]
    exact pruned_count_zero n q C hAO colour hz
  · exact (restoreStar_size n (pruned n q C) a b).trans
      (pruned_size_two n q s C hAO hqs hs hread')
  · exact restored_andPairs_lt n q r C hAO hq hqand hr hrand hcone a b hinputs

end PEqualNP.Outside.L_meta_4675.ProductiveStep
