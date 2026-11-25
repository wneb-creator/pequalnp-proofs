import or_seed_conjunction

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.SeedConjunction

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma seed_distinct : ∀ (q : Bool) (p : Fin 10), p ≠ 0 → p ≠ 1 →
    seed ≠ Extended.pins.getD 0 Extended.zero ∧
    seed ≠ Extended.pins.getD 1 Extended.zero ∧ seed ≠ extra q p := by decide +kernel

lemma lower_seed_used (q : Bool) (p : Fin 10) (h0 : p ≠ 0) (h1 : p ≠ 1) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank q p) (used : extra q p ∈ S) (seedUsed : seed ∈ S) : 17 ≤ k := by
  classical
  obtain ⟨needed0,needed1⟩ := endpoints_needed q p h0 h1 run raw
  obtain ⟨ne0,ne1⟩ := extra_distinct q p h0 h1
  obtain ⟨s0,s1,se⟩ := seed_distinct q p h0 h1
  have different : Extended.pins.getD 0 Extended.zero ≠ Extended.pins.getD 1 Extended.zero := by decide +kernel
  let front := Extended.pins.getD 0 Extended.zero :: Extended.pins.getD 1 Extended.zero :: seed :: extra q p ::
    ((((S.erase (Extended.pins.getD 0 Extended.zero)).erase
      (Extended.pins.getD 1 Extended.zero)).erase seed).erase (extra q p)).toList
  have nd : front.Nodup := by
    simp [front,different,different.symm,ne0,ne0.symm,ne1,ne1.symm,s0,s0.symm,s1,s1.symm,se,se.symm,Finset.nodup_toList,-List.getD_eq_getElem?_getD]
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.pins.getD 0 Extended.zero <;>
      by_cases hb : a = Extended.pins.getD 1 Extended.zero <;>
      by_cases hc : a = extra q p <;> by_cases hs : a = seed <;>
        simp [front,ha,hb,hc,hs,needed0,needed1,used,seedUsed,-List.getD_eq_getElem?_getD]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows slice01 (Extended.observe Extended.target) = Stronger.observe (graphGoal 383) := by
    rw [observe_projected01,projected_target]
  have properGoal : Stronger.proper (graphGoal 383) := by unfold Stronger.proper; decide +kernel
  have isZero : Stronger.observe Stronger.zero = fun _ => false := by
    funext r
    simp [Stronger.observe,Stronger.bit,Stronger.zero]
  have roots : supply true ((vars 383).map Stronger.observe)
      ((front.map Extended.observe).map (restrictRows slice01)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hm,rfl⟩ := List.mem_map.mp hin
    rw [observe_projected01]
    have hh := List.all_eq_true.mp (projected_bank q p) a
      (raw a (eqS ▸ List.mem_toFinset.mpr hm))
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    rcases hh with hz | hm
    · exact Or.inr (Or.inl ⟨false,hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)
  have need := projected_bound slice01 hrun (same ▸ Stronger.observe_proper properGoal)
    Reach.start roots (L:=13) (same ▸ low383)
  have charge : 4 ≤ mass ((front.map Extended.observe).map (restrictRows slice01)) := by
    have c0 : Constant (restrictRows slice01 (Extended.observe (Extended.pins.getD 0 Extended.zero))) := by
      rw [observe_projected01,show projected01 (Extended.pins.getD 0 Extended.zero)=Stronger.zero by decide +kernel]
      exact ⟨false,isZero⟩
    have c1 : Constant (restrictRows slice01 (Extended.observe (Extended.pins.getD 1 Extended.zero))) := by
      rw [observe_projected01,show projected01 (Extended.pins.getD 1 Extended.zero)=Stronger.zero by decide +kernel]
      exact ⟨false,isZero⟩
    have cs : Constant (restrictRows slice01 (Extended.observe seed)) := by
      rw [observe_projected01,show projected01 seed=Stronger.zero by decide +kernel]
      exact ⟨false,isZero⟩
    have ce : Constant (restrictRows slice01 (Extended.observe (extra q p))) := by
      rw [observe_projected01,projected_extra]
      exact ⟨false,isZero⟩
    simp only [front,List.map_cons,List.map_map,mass_cons,cost,c0,c1,cs,ce,ite_true]
    omega
  omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger.SeedConjunction
