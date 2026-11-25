import InputStructureClean

namespace PEqualNP.Outside.L_meta_2592_aux.WeightedLive
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open InputSlots Prune

lemma exists_minimal_live (n : ℕ) (C : Circuit) (fan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ Normal D ∧ weight D ≤ weight C ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ E : Circuit, FanInTwo E → Normal E → weight E ≤ weight C →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) → D.size ≤ E.size) ∧
      (∀ j, j < D.size → n + j ≠ D.output → n + j ∈ slots D) := by
  classical
  let P := fun s => ∃ D : Circuit, D.size = s ∧ FanInTwo D ∧ Normal D ∧
      weight D ≤ weight C ∧ ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hex : ∃ s, P s := by
    refine ⟨(normalize C).size, normalize C, rfl, normalize_fan C fan, normalize_normal C, ?_, ?_⟩
    · exact le_of_eq (normalize_weight C)
    · exact fun x => normalize_eval C (List.ofFn x)
  obtain ⟨D, hsize, hfan, hnorm, hweight, heval⟩ := Nat.find_spec hex
  have hminimal : ∀ E : Circuit, FanInTwo E → Normal E → weight E ≤ weight C →
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x)) → D.size ≤ E.size := by
    intro E hEfan hEnorm hEweight hEeval
    rw [hsize]
    exact Nat.find_min' hex ⟨E, rfl, hEfan, hEnorm, hEweight, hEeval⟩
  refine ⟨D, hfan, hnorm, hweight, heval, hminimal, ?_⟩
  intro j hj ho
  by_contra hdead
  obtain ⟨pre, g, post, hsplit, hlen⟩ := split_at D.gates j hj
  have hD : D = ⟨pre ++ g :: post, D.output⟩ := by cases D; simp_all
  have hno : ∀ q ∈ post, n + pre.length ∉ q.inputs := by
    intro q hq hm
    have hqD : q ∈ D.gates := by rw [hsplit]; simp [hq]
    apply hdead
    apply List.mem_flatMap.mpr
    refine ⟨q, hqD, ?_⟩
    rw [effective_eq D hnorm q hqD]
    simpa [hlen] using hm
  let E := Prune.drop n pre post D.output
  have hEfan : FanInTwo E := drop_fan n pre g post D.output (hD ▸ hfan)
  have hEnorm : Normal E := drop_normal n pre post g D.output (hD ▸ hnorm)
  have hEweight : weight E ≤ weight C := by
    have h := drop_weight n pre post g D.output
    rw [← hD] at h
    exact h.trans hweight
  have hEeval : ∀ x : Fin n → Bool, E.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    have h := drop_eval n pre g post D.output hno (by omega) (List.ofFn x) (by simp)
    rw [← hD] at h
    exact h.trans (heval x)
  have hmin : Nat.find hex ≤ E.size := Nat.find_min' hex
    ⟨E, rfl, hEfan, hEnorm, hEweight, hEeval⟩
  have hs := drop_size n pre post g D.output
  rw [← hD] at hs
  change E.size + 1 = D.size at hs
  omega


end PEqualNP.Outside.L_meta_2592_aux.WeightedLive

namespace PEqualNP.Outside.L_meta_2592_aux.WeightedPetersen
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open InputSlots Prune WeightedLive

lemma minimal_unique_reader (C : Circuit) (fan : FanInTwo C)
    (budget : C.size ≤ 19) (hasNot : 1 ≤ NotBracket.notCount C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    ∃ (D : Circuit) (i : Fin 10) (q : ℕ), FanInTwo D ∧ Normal D ∧ weight D ≤ 19 ∧
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x) ∧
      (∀ E : Circuit, FanInTwo E → Normal E → weight E ≤ weight D →
        (∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = petersen x) → D.size ≤ E.size) ∧
      q < D.gates.length ∧ i.val ∈ (D.gates.getD q ⟨GateOp.or, []⟩).inputs ∧
      ∀ t, t < D.gates.length → t ≠ q → i.val ∉ (D.gates.getD t ⟨GateOp.or, []⟩).inputs := by
  obtain ⟨D, hfan, hnorm, hweight, heval, hminimal, hlive⟩ := exists_minimal_live 10 C fan
  have hCweight : weight C ≤ 19 := by unfold weight; simp [show NotBracket.notCount C ≠ 0 by omega]; omega
  have hw : weight D ≤ 19 := hweight.trans hCweight
  have hc : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := fun x => (heval x).trans (correct x)
  have hb : D.size + 1 < 2 * 10 + NotBracket.notCount D := by
    unfold weight at hw
    split_ifs at hw <;> omega
  obtain ⟨i, hi, hone⟩ := input_once D 10 hfan (essential D hnorm hc) hlive hb
  obtain ⟨q, hq, hread, hother⟩ := unique_reader D.gates i hone
  have get_mem : ∀ t, t < D.gates.length → D.gates.getD t ⟨GateOp.or, []⟩ ∈ D.gates := by
    intro t ht
    rw [List.getD_eq_getElem _ _ ht]
    exact List.getElem_mem ht
  have hm : ∀ E : Circuit, FanInTwo E → Normal E → weight E ≤ weight D →
      (∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = petersen x) → D.size ≤ E.size := by
    intro E hEfan hEnorm hEweight hEeval
    exact hminimal E hEfan hEnorm (hEweight.trans hweight)
      (fun x => (hEeval x).trans (correct x).symm)
  refine ⟨D, ⟨i, hi⟩, q, hfan, hnorm, hw, hc, hm, hq, ?_, ?_⟩
  · rwa [effective_eq D hnorm _ (get_mem q hq)] at hread
  · intro t ht hne
    have h := hother t ht hne
    rwa [effective_eq D hnorm _ (get_mem t ht)] at h


end PEqualNP.Outside.L_meta_2592_aux.WeightedPetersen
