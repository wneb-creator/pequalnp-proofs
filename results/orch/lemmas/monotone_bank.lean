import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_1886_aux.MonoBank
open PEqualNP.Outside.L_meta_2592_aux.Stronger
open CanonicalBank

lemma first_needed {u : Bool} (d : Fin 4) (j : Fin 2) {k S}
    (run : Extended.Live u Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) : Extended.first ∈ S := by
  obtain ⟨a,ha,hchange⟩ := Extended.live_row_difference run (target_diff d j)
  have chk := List.all_eq_true.mp (other_stable d j) a (raw a ha)
  simp only [Bool.or_eq_true,beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

lemma lower {u : Bool} {L : Nat} (floor : Lower u inputs graph L) (d : Fin 4) (j : Fin 2) {k S}
    (run : Extended.Live u Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) : L + 1 ≤ k := by
  classical
  have hfirst := first_needed d j run raw
  let front := Extended.first :: (S.erase Extended.first).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp,Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> simp [front,ha,hfirst]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe,bit,zero]
  have supplyRoots : supply u (inputs.map observe) ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmFront,rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    have hh := List.all_eq_true.mp (projected_bank d j) a (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    rcases hh with hz|hm
    · exact Or.inr (Or.inl ⟨false,hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=L) (same ▸ floor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first=zero by decide +kernel]
      exact ⟨false,isZero⟩
    simp [front,mass_cons,cost,ac]
  omega

lemma conjunction_lower {u : Bool} {L : Nat} (floor : Lower u inputs graph L) (d : Fin 4) (j : Fin 2) (hd : d = 0 ∨ d = 2) {k S}
    (run : Extended.Live u Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) (used : extra d j ∈ S) : L + 2 ≤ k := by
  classical
  have hfirst := first_needed d j run raw
  have hne := extra_ne_first d j
  let front := Extended.first :: extra d j :: ((S.erase Extended.first).erase (extra d j)).toList
  have nd : front.Nodup := by
    simp [front, hne, hne.symm, Finset.nodup_toList]
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = Extended.first <;> by_cases hb : a = extra d j <;>
      simp [front,ha,hb,hfirst,used]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have isZero : observe zero = fun _ => false := by funext r; simp [observe,bit,zero]
  have supplyRoots : supply u (inputs.map observe) ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_,hin,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmFront,rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    have hh := List.all_eq_true.mp (projected_bank d j) a (raw a (eqS ▸ List.mem_toFinset.mpr hmFront))
    simp only [Bool.or_eq_true,beq_iff_eq] at hh
    rcases hh with hz|hm
    · exact Or.inr (Or.inl ⟨false,hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_,by simpa using hm,rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L:=L) (same ▸ floor)
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first=zero by decide +kernel]
      exact ⟨false,isZero⟩
    have bc : Constant (restrictRows embed (Extended.observe (extra d j))) := by
      rw [observe_projected, extra_projects_zero d hd j]
      exact ⟨false,isZero⟩
    simp only [front,List.map_cons,List.map_map,mass_cons,cost,ac,bc,ite_true]
    omega
  omega

end PEqualNP.Outside.L_meta_1886_aux.MonoBank
