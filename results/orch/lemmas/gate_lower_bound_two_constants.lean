namespace PEqualNP.Outside.L_meta_2592_aux.GateFirst

lemma tail_two_constants_floor {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, projected a = zero ∨ projected a ∈ inputs)
    (z w : Extended.Sig) (hz : z ∈ S) (hw : w ∈ S) (different : z ≠ w)
    (zeroZ : projected z = zero) (zeroW : projected w = zero) : 17 ≤ k := by
  classical
  let front := z :: w :: ((S.erase z).erase w).toList
  have nd : front.Nodup := by
    simp [front, different, Finset.nodup_toList]
  have eqS : front.toFinset = S := by
    ext a
    by_cases az : a = z <;> by_cases aw : a = w <;> simp [front, az, aw, hz, hw]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe, bit, zero]
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    rcases raw a (eqS ▸ List.mem_toFinset.mpr hmFront) with hzero | hm
    · exact Or.inr (Or.inl ⟨false, hzero ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, hm, rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have az : Constant (restrictRows embed (Extended.observe z)) := by
      rw [observe_projected, zeroZ]
      exact ⟨false, isZero⟩
    have aw : Constant (restrictRows embed (Extended.observe w)) := by
      rw [observe_projected, zeroW]
      exact ⟨false, isZero⟩
    simp only [front, List.map_cons, mass_cons, cost, if_pos az, if_pos aw]
    omega
  omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
lemma first_absorbing_data : ∀ (d : Fin 4) (j : Fin 10),
    (d = 0 ∨ d = 2) → j ≠ 0 →
    projected (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) = zero ∧
      Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero) ≠ Extended.first := by
  decide +kernel

lemma first_live_absorbing_floor (d : Fin 4) (j : Fin 10) (hd : d = 0 ∨ d = 2)
    (distinct : j ≠ 0) {k : Nat} {U : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k
      (insert (Extended.bin d.val Extended.first (Extended.initial.getD j.val Extended.zero)) U))
    (raw : ∀ a ∈ U, a ∈ Extended.initial) : 17 ≤ k := by
  have retained := first_live_retained d j distinct run raw
  obtain ⟨zeroZ, different⟩ := first_absorbing_data d j hd distinct
  have permitted : Extended.initial.all
      (fun a => (projected a == zero) || inputs.contains (projected a)) = true := by
    decide +kernel
  apply tail_two_constants_floor run _ _ Extended.first (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem retained) different zeroZ (by decide +kernel)
  intro a ha
  rcases Finset.mem_insert.mp ha with eq | hm
  · exact Or.inl (eq.symm ▸ zeroZ)
  · have hh := List.all_eq_true.mp permitted a (raw a hm)
    simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using hh

end PEqualNP.Outside.L_meta_2592_aux.GateFirst
