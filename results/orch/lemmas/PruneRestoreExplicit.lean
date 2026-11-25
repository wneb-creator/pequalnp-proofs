namespace PEqualNP.Outside.L_meta_4675.PruneRestoreExplicit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.PruningPrefix
open PEqualNP.Outside.L_meta_4675.PruningTrace
open PEqualNP.Outside.L_meta_4675.PruneRestore
open PEqualNP.Outside.L_meta_4675.StarAppendOptional

lemma restore_explicit (n q r a b : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (colour : ℕ → Bool) (hAO : IsAO2 n C) (hz : tCount n C colour = 0)
    (hqr : q < r) (hr : r < C.gates.length) (hread : n + q ∈ C.gates[r].inputs)
    (ha : a < n + q) (hb : b < n + q)
    (hunit : ∀ i : Fin n, f (fun k => decide (k = i)) = false)
    (hsemantic : ∀ x : Fin n → Bool,
      f x = ((forcedValues n q C (List.ofFn x)).getD C.output false ||
        ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false))) :
    let D := restoreStar n (pruned n q C) a b
    IsAO2 n D ∧ tCount n D colour = 0 ∧ D.size ≤ C.size ∧ circuitFun n D = f := by
  have hq : q ≤ C.gates.length := by omega
  have hAP := pruned_ao n q C hAO
  have hap := prior_wire_valid n q C hAO hq a ha
  have hbp := prior_wire_valid n q C hAO hq b hb
  have hreach : orIn n (pruned n q C) (pruned n q C).output = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    let x : Fin n → Bool := fun k => decide (k = i)
    have hv := PEqualNP.Outside.L_meta_4675.MaskingNext.orIn_true n (pruned n q C)
      hAP x (pruned n q C).output i hi (by simp [x])
    change (pruned n q C).eval (List.ofFn x) = true at hv
    have he := hsemantic x
    rw [← pruned_eval n q C hAO (List.ofFn x) (by simp), hv] at he
    have hf : f x = false := hunit i
    rw [hf] at he
    simp at he
  refine ⟨restoreStar_ao n _ a b hAP hap hbp, ?_, ?_, ?_⟩
  · rw [restoreStar_tCount n _ a b colour hAP hap hbp hreach]
    exact pruned_count_zero n q C hAO colour hz
  · exact (restoreStar_size n (pruned n q C) a b).trans
      (pruned_size_two n q r C hAO hqr hr hread)
  · funext x
    change (restoreStar n (pruned n q C) a b).eval (List.ofFn x) = f x
    rw [restoreStar_eval n _ a b (List.ofFn x) (by simp),
      pruned_eval n q C hAO (List.ofFn x) (by simp),
      pruned_wire_before n q C hAO hq (List.ofFn x) (by simp) a ha,
      pruned_wire_before n q C hAO hq (List.ofFn x) (by simp) b hb]
    exact (hsemantic x).symm

end PEqualNP.Outside.L_meta_4675.PruneRestoreExplicit
