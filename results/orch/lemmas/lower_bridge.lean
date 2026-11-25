namespace PEqualNP.Outside.L_meta_14985_aux.GraphTarget8
open PEqualNP.Outside.L_meta_14985_aux
open PEqualNP.Outside.L_meta_14985_aux.LiveCircuits
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def sample8 (r : Row) (j : Fin 8) := bit r (cols8.getD j.val zero)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma eightTable : ∀ r : Row, bit r full8 = graphFn (sample8 r) := by decide +kernel

lemma eightList : List.ofFn (fun i : Fin 8 => cols8.getD i.val zero) = cols8 := rfl

lemma eightSampled (r : Row) : List.ofFn (sample8 r) = cols8.map (bit r) := by
  rw [←eightList, List.map_ofFn]
  rfl

lemma eval8 (C : Circuit) (h : FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates cols8).getD i zero) =
      (C.wires (List.ofFn (sample8 r))).getD i false := by
  rw [←b_read, execute_bits _ _ _ (fun g hg => (h g hg).1), eightSampled]
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
lemma binaryLower8 (low : Lower true cols8 full8 10) (C : Circuit) (legal : FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graphFn x) :
    10 ≤ C.gates.countP (fun g => !isNot g) := by
  classical
  have goalEq : (execute C.gates cols8).getD C.output zero = full8 := by
    apply bit_ext
    intro r
    exact (eval8 C legal C.output r).trans ((computes (sample8 r)).trans (eightTable r).symm)
  have rep := get_rep (u := true) (execute C.gates cols8) C.output
  rw [goalEq] at rep
  unfold PEqualNP.Outside.L_meta_14985_aux.LiveCircuits.Repr at rep
  have pg : bit 0 full8 = false := by decide +kernel
  have pfull : proper full8 := by unfold proper; decide +kernel
  rw [nrm_id pg] at rep
  obtain ⟨k, S, hk, run, sub⟩ := extract C.gates cols8 legal (by simp) pfull
    (rep.resolve_right (fun h => h pfull))
  have plain : cols8.all plainWord = true := by decide +kernel
  rw [nrm_map plain] at sub
  have rs := list_run run S.toList (Finset.nodup_toList _) (Finset.toList_toFinset _)
  have hs : supply true (cols8.map observe)
      ((S.toList.map observe).map (restrictRows (id : Row → Row))) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact Or.inl (List.mem_map_of_mem (sub _ (Finset.mem_toList.mp ha)))
  have b := projected_bound (id : Row → Row) rs (observe_proper pfull) Reach.start hs (L := 10) low
  omega

lemma gateLower8 (low : Lower true cols8 full8 10) (C : Circuit) (legal : FanInTwo C)
    (negUsed : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graphFn x) :
    11 ≤ C.gates.length := by
  obtain ⟨g, hg, ng⟩ := negUsed
  have hc := binaryLower8 low C legal computes
  by_contra! h
  have all := (List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length
    (by omega : C.gates.length ≤ C.gates.countP (fun g => !isNot g)))) g hg
  simp [isNot, ng] at all

lemma finish8 (low : Lower true cols8 full8 10) : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 4, 1, 4, 0, 5, 1, 5, 0, 6, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o legal _uniq computes
  change ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x) = graphFn x at computes
  by_cases hn : ∃ g ∈ gates, g.op = GateOp.not
  · have hl : FanInTwo ⟨gates, o⟩ := by
      intro g hg
      obtain ⟨ht, hw⟩ := legal g hg
      exact ⟨by simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using ht, hw⟩
    have hs := gateLower8 low ⟨gates, o⟩ hl hn computes
    exact ⟨graphWit.gates, graphWit.output, graphWitLegal, hs, graphWitEval⟩
  · refine ⟨gates, o, ?_, Nat.le_refl _, computes⟩
    intro g hg
    obtain ⟨hor, hw⟩ := legal g hg
    rcases hor with ha | ho | hnot
    · exact ⟨Or.inl ha, hw⟩
    · exact ⟨Or.inr ho, hw⟩
    · exact (hn ⟨g, hg, hnot⟩).elim

end PEqualNP.Outside.L_meta_14985_aux.GraphTarget8
