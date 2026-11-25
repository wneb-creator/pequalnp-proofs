namespace PEqualNP.Outside.L_meta_2590_aux.MonoNine

def canonicalDoubleExtra (j : Fin 2) (c : Fin 10) (dep : Bool) : Extended.Sig :=
  Extended.bin 0 (if dep then canonicalExtra j 0 else Extended.first)
    (Extended.pins.getD c.val Extended.zero)

def doubleRoots (j : Fin 2) (c : Fin 10) (dep : Bool) : List Extended.Sig :=
  Extended.pins ++ [canonicalExtra j 0, canonicalDoubleExtra j c dep]

def doubleWitnessA (c : Fin 10) : Extended.Row := if c.val = 5 then 64 else 16

def doubleWitnessB (c : Fin 10) : Extended.Row := doubleWitnessA c + 512

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma doubleWitness : ∀ (j : Fin 2) (c : Fin 10) (dep : Bool),
    Extended.bit (doubleWitnessA c) Extended.target ≠ Extended.bit (doubleWitnessB c) Extended.target ∧
    (doubleRoots j c dep).all (fun a =>
      (Extended.bit (doubleWitnessA c) a == Extended.bit (doubleWitnessB c) a) ||
      (a == Extended.first)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma doubleProjects : ∀ (j : Fin 2) (c : Fin 10) (dep : Bool),
    (doubleRoots j c dep).all (fun a =>
      (projected a == zero) || inputs.contains (projected a)) = true := by decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma doubleZero : ∀ (j : Fin 2) (c : Fin 10) (dep : Bool),
    (dep = true ∨ c ≠ 0) → projected (canonicalDoubleExtra j c dep) = zero ∧
    canonicalDoubleExtra j c dep ≠ Extended.first := by decide +kernel

lemma firstNeededDouble (j : Fin 2) (c : Fin 10) (dep : Bool) {k S}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ doubleRoots j c dep) : Extended.first ∈ S := by
  obtain ⟨a, ha, hchange⟩ := Extended.live_row_difference run (doubleWitness j c dep).1
  have chk := List.all_eq_true.mp (doubleWitness j c dep).2 a (raw a ha)
  simp only [Bool.or_eq_true, beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

lemma doubleSuffixEighteen (j : Fin 2) (c : Fin 10) (dep : Bool)
    (hdep : dep = true ∨ c ≠ 0) {k S}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ doubleRoots j c dep)
    (hextra : canonicalDoubleExtra j c dep ∈ S) : 18 ≤ k := by
  classical
  have hfirst := firstNeededDouble j c dep run raw
  have hne := (doubleZero j c dep hdep).2
  let front := Extended.first :: canonicalDoubleExtra j c dep ::
    ((S.erase Extended.first).erase (canonicalDoubleExtra j c dep)).toList
  have nd : front.Nodup := by
    simp [front, hne, Ne.symm hne]
    exact Finset.nodup_toList _
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> by_cases hb : a = canonicalDoubleExtra j c dep <;>
      simp [front, ha, hb, hfirst, hextra]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe, bit, zero]
  have supplyRoots : supply false (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    have hh := List.all_eq_true.mp (doubleProjects j c dep) a
      (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true, beq_iff_eq] at hh
    rcases hh with hz | hm
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, by simpa using hm, rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 16) (same ▸ monoNineFloor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, isZero⟩
    have bc : Constant (restrictRows embed (Extended.observe (canonicalDoubleExtra j c dep))) := by
      rw [observe_projected, (doubleZero j c dep hdep).1]
      exact ⟨false, isZero⟩
    simp [front, mass_cons, cost, ac, bc]
    omega
  omega

end PEqualNP.Outside.L_meta_2590_aux.MonoNine
