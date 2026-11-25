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
