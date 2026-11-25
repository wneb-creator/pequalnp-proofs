namespace PEqualNP.Outside.L_meta_2592.Signed

lemma dependent_and_floor (negate : Bool) (i j c : Fin 10)
    (ij : i ≠ j) (ic : i ≠ c) (jc : j ≠ c)
    {k : Nat} {S : Finset Extended.Sig}
    (kept : Extended.bin (if negate then 3 else 0)
      (Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero)) (Extended.pins.getD c.val Extended.zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ∨
      v = Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
        (Extended.pins.getD j.val Extended.zero) ∨
      v = Extended.bin (if negate then 3 else 0)
        (Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
          (Extended.pins.getD j.val Extended.zero)) (Extended.pins.getD c.val Extended.zero))
    (run : Extended.Live true Extended.target k S) : 16 ≤ k := by
  let a := Extended.pins.getD i.val Extended.zero
  let b := Extended.pins.getD j.val Extended.zero
  let cPin := Extended.pins.getD c.val Extended.zero
  let s := Extended.bin 1 a b
  let z := Extended.bin (if negate then 3 else 0) s cPin
  have aMem : a ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨i, rfl⟩
  have bMem : b ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨j, rfl⟩
  have cMem : cPin ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨c, rfl⟩
  have retained : cPin ∈ S := Extended.dependent_and_keep_input negate i j c ij ic jc raw run
  obtain ⟨rows, fixed, same, supplied⟩ := pin_projection_false cPin cMem
  let projectedS := restrictRows rows (Extended.observe s)
  have suppliedOr : Reach true (inputs.map observe) 1 (projectedS :: inputs.map observe) := by
    have step := Reach.two true Reach.start (supplied a aMem) (supplied b bMem)
    change Reach true (inputs.map observe) 1
      (restrictRows rows (Extended.observe (Extended.bin 1 a b)) :: inputs.map observe)
    rw [Extended.obs_bin, restrict_comb]
    exact step
  have gateZero : restrictRows rows (Extended.observe z) = (fun _ => false) := by
    change restrictRows rows (Extended.observe (Extended.bin (if negate then 3 else 0) s cPin)) = _
    rw [Extended.obs_bin, restrict_comb, fixed]
    cases negate <;> funext r <;> simp [comb, combine]
  have floor := live_two_constants_cost_bound run rows same
    (Extended.pin_ne_dependent_and negate i j c ij ic jc) retained kept
    ⟨false, fixed⟩ ⟨false, gateZero⟩ suppliedOr (by
      intro v hv
      rcases raw v hv with ordinary | rfl | rfl
      · exact available_cons projectedS (supplied v ordinary)
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (Or.inl ⟨false, gateZero⟩))
  omega

end PEqualNP.Outside.L_meta_2592.Signed
