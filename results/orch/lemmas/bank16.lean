import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger

namespace CanonicalBank

def extra (d : Fin 4) (j : Fin 2) : Extended.Sig :=
  Extended.bin d.val (Extended.pins.getD 0 Extended.zero)
    (Extended.pins.getD (j.val + 1) Extended.zero)

def bank (d : Fin 4) (j : Fin 2) : List Extended.Sig :=
  Extended.pins ++ [extra d j]

def witness (d : Fin 4) (j : Fin 2) : Fin 512 :=
  if d = 0 ∨ d = 3 then 16 else if j = 0 then 128 else 48

def lo (d : Fin 4) (j : Fin 2) : Extended.Row :=
  ⟨(witness d j).val, by have := (witness d j).isLt; omega⟩

def hi (d : Fin 4) (j : Fin 2) : Extended.Row :=
  ⟨(witness d j).val + 512, by have := (witness d j).isLt; omega⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma target_diff : ∀ d : Fin 4, ∀ j : Fin 2,
    Extended.bit (lo d j) Extended.target ≠ Extended.bit (hi d j) Extended.target := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma other_stable : ∀ d : Fin 4, ∀ j : Fin 2,
    (bank d j).all (fun a =>
      (Extended.bit (lo d j) a == Extended.bit (hi d j) a) ||
      (a == Extended.first)) = true := by
  decide +kernel

lemma first_needed (d : Fin 4) (j : Fin 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) : Extended.first ∈ S := by
  obtain ⟨a,ha,hchange⟩ := Extended.live_row_difference run (target_diff d j)
  have chk := List.all_eq_true.mp (other_stable d j) a (raw a ha)
  simp only [Bool.or_eq_true,beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma projected_bank : ∀ d : Fin 4, ∀ j : Fin 2,
    (bank d j).all (fun a => (projected a == zero) || inputs.contains (projected a)) = true := by
  decide +kernel

lemma lower (d : Fin 4) (j : Fin 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) : 16 ≤ k := by
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
  have supplyRoots : supply true (inputs.map observe) ((front.map Extended.observe).map (restrictRows embed)) := by
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
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first=zero by decide +kernel]
      exact ⟨false,isZero⟩
    simp [front,mass_cons,cost,ac]
  omega

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma extra_ne_first : ∀ d : Fin 4, ∀ j : Fin 2, extra d j ≠ Extended.first := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma extra_projects_zero : ∀ d : Fin 4, d = 0 ∨ d = 2 → ∀ j : Fin 2,
    projected (extra d j) = zero := by
  decide +kernel

lemma conjunction_lower (d : Fin 4) (j : Fin 2) (hd : d = 0 ∨ d = 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) (used : extra d j ∈ S) : 17 ≤ k := by
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
  have supplyRoots : supply true (inputs.map observe) ((front.map Extended.observe).map (restrictRows embed)) := by
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
    Reach.start supplyRoots (L:=15) (same ▸ nineFloor)
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

end CanonicalBank

end PEqualNP.Outside.L_meta_2592_aux.Stronger
