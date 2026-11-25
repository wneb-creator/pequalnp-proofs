namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

def canonicalExtra (j : Fin 2) (d : Fin 4) : Extended.Sig :=
  Extended.bin d.val (Extended.pins.getD 0 Extended.zero)
    (Extended.pins.getD (j.val + 1) Extended.zero)

def canonicalWitnessA (j : Fin 2) (d : Fin 4) : Extended.Row :=
  if d.val = 0 ∨ d.val = 3 then 16 else if j.val = 0 then 128 else 48

def canonicalWitnessB (j : Fin 2) (d : Fin 4) : Extended.Row := canonicalWitnessA j d + 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma canonicalWitness : ∀ (j : Fin 2) (d : Fin 4),
    Extended.bit (canonicalWitnessA j d) Extended.target ≠ Extended.bit (canonicalWitnessB j d) Extended.target ∧
    (Extended.pins ++ [canonicalExtra j d]).all (fun a =>
      (Extended.bit (canonicalWitnessA j d) a == Extended.bit (canonicalWitnessB j d) a) ||
      (a == Extended.first)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma canonicalProjects : ∀ (j : Fin 2) (d : Fin 4),
    (Extended.pins ++ [canonicalExtra j d]).all (fun a =>
      (projected a == zero) || inputs.contains (projected a)) = true := by decide +kernel

lemma firstNeededCanonical (j : Fin 2) (d : Fin 4) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ++ [canonicalExtra j d]) : Extended.first ∈ S := by
  obtain ⟨a, ha, hchange⟩ := Extended.live_row_difference run (canonicalWitness j d).1
  have chk := List.all_eq_true.mp (canonicalWitness j d).2 a (raw a ha)
  simp only [Bool.or_eq_true, beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

lemma suffixSixteen (j : Fin 2) (d : Fin 4) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins ++ [canonicalExtra j d]) : 16 ≤ k := by
  classical
  have hfirst := firstNeededCanonical j d run raw
  let front := Extended.first :: (S.erase Extended.first).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> simp [front, ha, hfirst]
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
    have hh := List.all_eq_true.mp (canonicalProjects j d) a
      (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true, beq_iff_eq] at hh
    rcases hh with hz | hm
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, isZero⟩
    simp [front, mass_cons, cost, ac]
  omega

end PEqualNP.Outside.L_meta_2592_aux.Binary16
