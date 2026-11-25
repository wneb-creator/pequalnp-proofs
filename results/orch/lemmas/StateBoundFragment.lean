namespace PEqualNP.Outside.L_meta_2592.Signed

lemma live_one_constant_bound {k : Nat} {S : Finset Extended.Sig} {a : Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (rows : Row → Extended.Row)
    (same : restrictRows rows (Extended.observe Extended.target) = observe graph)
    (member : a ∈ S)
    (fixed : Constant (restrictRows rows (Extended.observe a)))
    (supplied : ∀ v ∈ S,
      Available true (inputs.map observe) (restrictRows rows (Extended.observe v))) :
    16 ≤ k := by
  classical
  let front := a :: (S.erase a).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext v
    by_cases va : v = a <;> simp [front, va, member]
  have hrun := Extended.list_run run front nd eqS
  have sup : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows rows)) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    exact supplied z (eqS ▸ List.mem_toFinset.mpr hz)
  have bound := projected_bound rows hrun (same ▸ observe_proper graph_proper)
    Reach.start sup (L := 15) (by
      intro q bs reach hit
      apply nineFloor q bs reach
      rwa [same] at hit)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows rows)) := by
    simp [front, mass_cons, cost, fixed]
  omega

end PEqualNP.Outside.L_meta_2592.Signed
