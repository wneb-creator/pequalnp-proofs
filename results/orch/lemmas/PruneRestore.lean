namespace PEqualNP.Outside.L_meta_4675.PruneRestore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.Pruning
open PEqualNP.Outside.L_meta_4675.PruningPrefix
open PEqualNP.Outside.L_meta_4675.PruningTrace
open PEqualNP.Outside.L_meta_4675.StarAppendOptional

lemma prior_wire_valid (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hq : q ≤ C.gates.length) (w : ℕ) (hw : w < n + q) :
    w < n + (pruned n q C).gates.length := by
  have hv := (compiled_valid_related n q C hAO (List.replicate n false) (by simp)).1
  have hb := bounded_getD n (compiled n q C.gates) hv.2 w
  exact hb w (alias_before n q C hAO hq w hw)

lemma prune_then_restore (n q r a b : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (colour : ℕ → Bool) (hAO : IsAO2 n C) (hz : tCount n C colour = 0)
    (hqr : q < r) (hr : r < C.gates.length) (hread : n + q ∈ C.gates[r].inputs)
    (ha : a < n + q) (hb : b < n + q)
    (hreach : orIn n (pruned n q C) (pruned n q C).output = ∅)
    (hsemantic : ∀ x : Fin n → Bool,
      f x = ((forcedValues n q C (List.ofFn x)).getD C.output false ||
        ((C.wires (List.ofFn x)).getD a false && (C.wires (List.ofFn x)).getD b false))) :
    ∃ D : Circuit, IsAO2 n D ∧ tCount n D colour = 0 ∧ D.size ≤ C.size ∧ circuitFun n D = f := by
  have hq : q ≤ C.gates.length := by omega
  have hAP := pruned_ao n q C hAO
  have hap := prior_wire_valid n q C hAO hq a ha
  have hbp := prior_wire_valid n q C hAO hq b hb
  let D := restoreStar n (pruned n q C) a b
  refine ⟨D, restoreStar_ao n _ a b hAP hap hbp, ?_, ?_, ?_⟩
  · change tCount n (restoreStar n (pruned n q C) a b) colour = 0
    rw [restoreStar_tCount n _ a b colour hAP hap hbp hreach]
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

end PEqualNP.Outside.L_meta_4675.PruneRestore
