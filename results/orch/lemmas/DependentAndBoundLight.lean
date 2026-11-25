import PEqualNP.Outside.L_meta_2592
namespace PEqualNP.Outside.L_meta_2592.Signed

lemma live_two_constants_cost_bound {k : Nat} {S : Finset Extended.Sig} {a b : Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (rows : Row → Extended.Row)
    (same : restrictRows rows (Extended.observe Extended.target) = observe graph)
    (distinct : a ≠ b) (member : a ∈ S) (memberB : b ∈ S)
    (fixed : Constant (restrictRows rows (Extended.observe a)))
    (fixedB : Constant (restrictRows rows (Extended.observe b)))
    {steps : Nat} {bank : List (Wire Row)}
    (reach : Reach true (inputs.map observe) steps bank)
    (supplied : ∀ v ∈ S,
      Available true bank (restrictRows rows (Extended.observe v))) :
    17 ≤ steps + k := by
  classical
  let front := a :: b :: ((S.erase a).erase b).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    constructor
    · simp [distinct]
    · apply List.nodup_cons.mpr
      exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext v
    by_cases va : v = a <;> by_cases vb : v = b <;> simp [front, va, vb, member, memberB]
  have hrun := Extended.list_run run front nd eqS
  have sup : supply true bank
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    exact supplied z (eqS ▸ List.mem_toFinset.mpr hz)
  have bound := projected_bound rows hrun (same ▸ observe_proper graph_proper)
    reach sup (L := 15) (by
      intro q bs reach hit
      apply nineFloor q bs reach
      rwa [same] at hit)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp [front, mass_cons, cost, fixed, fixedB]
    omega
  omega

end PEqualNP.Outside.L_meta_2592.Signed
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
    (run : Extended.Live true Extended.target k S)
    (keepRaw : Extended.pins.getD c.val Extended.zero ∈ S)
    (different : Extended.pins.getD c.val Extended.zero ≠
      Extended.bin (if negate then 3 else 0)
        (Extended.bin 1 (Extended.pins.getD i.val Extended.zero)
          (Extended.pins.getD j.val Extended.zero)) (Extended.pins.getD c.val Extended.zero)) : 16 ≤ k := by
  let a := Extended.pins.getD i.val Extended.zero
  let b := Extended.pins.getD j.val Extended.zero
  let cPin := Extended.pins.getD c.val Extended.zero
  let s := Extended.bin 1 a b
  let z := Extended.bin (if negate then 3 else 0) s cPin
  have aMem : a ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨i, rfl⟩
  have bMem : b ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨j, rfl⟩
  have cMem : cPin ∈ Extended.pins := (Extended.pin_mem _).mpr ⟨c, rfl⟩
  have retained : cPin ∈ S := keepRaw
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
    different retained kept
    ⟨false, fixed⟩ ⟨false, gateZero⟩ suppliedOr (by
      intro v hv
      rcases raw v hv with ordinary | rfl | rfl
      · exact available_cons projectedS (supplied v ordinary)
      · exact Or.inl List.mem_cons_self
      · exact Or.inr (Or.inl ⟨false, gateZero⟩))
  omega

end PEqualNP.Outside.L_meta_2592.Signed
