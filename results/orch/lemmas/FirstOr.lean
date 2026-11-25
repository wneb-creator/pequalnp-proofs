import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113FirstOr

open PEqualNP.Outside.L_meta_6581

abbrev pin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

def witnessRow (j : Fin 10) : Extended.Row :=
  ![0, 192, 96, 384, 192, 144, 68, 129, 136, 130] j

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma witness_data : ∀ j : Fin 10, j ≠ 0 →
    Extended.bit (witnessRow j) Extended.target ≠
      Extended.bit (witnessRow j + 512) Extended.target ∧
    Extended.bit (witnessRow j) (Extended.bin 1 Extended.first (pin j)) =
      Extended.bit (witnessRow j + 512) (Extended.bin 1 Extended.first (pin j)) ∧
    Extended.initial.all (fun a => (a == Extended.first) ||
      (Extended.bit (witnessRow j) a ==
        Extended.bit (witnessRow j + 512) a)) = true := by
  decide +kernel

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma pin_mem (j : Fin 10) : pin j ∈ Extended.initial := by
  revert j
  decide +kernel

lemma first_or_retained (j : Fin 10) (hj : j ≠ 0) {k : Nat}
    {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin 1 Extended.first (pin j)) U)) :
    Extended.first ∈ U := by
  obtain ⟨different, same, onlyFirst⟩ := witness_data j hj
  obtain ⟨a, ha, changes⟩ := Extended.live_row_difference tailRun different
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact False.elim (changes same)
  · have hc := List.all_eq_true.mp onlyFirst a (raw a ha)
    simp only [Bool.or_eq_true, beq_iff_eq] at hc
    exact hc.resolve_right changes ▸ ha

lemma projected_first_or (j : Fin 10) :
    projected (Extended.bin 1 Extended.first (pin j)) = projected (pin j) := by
  change (Extended.first ||| pin j).setWidth 512 = (pin j).setWidth 512
  rw [BitVec.setWidth_or]
  have hz : Extended.first.setWidth 512 = (0 : BitVec 512) := by decide +kernel
  rw [hz]
  simp

lemma first_or_tail_sixteen (j : Fin 10) {k : Nat} {T : Finset Extended.Sig}
    (tailRun : Extended.Live true Extended.target k T)
    (firstPresent : Extended.first ∈ T)
    (raw : ∀ a ∈ T, a ∈ Extended.initial ∨ a = Extended.bin 1 Extended.first (pin j)) :
    16 ≤ k := by
  classical
  let front := Extended.first :: (T.erase Extended.first).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqT : front.toFinset = T := by
    ext a
    by_cases ha : a = Extended.first <;> simp [front, ha, firstPresent]
  have hrun := Extended.list_run tailRun front nd eqT
  have same : restrictRows embed (Extended.observe Extended.target) = observe graph := by
    rw [observe_projected]
    exact congrArg observe (by decide +kernel)
  have base : Extended.initial.all
      (fun a => (projected a == zero) || inputs.contains (projected a)) = true := by
    decide +kernel
  have permitted (a : Extended.Sig) (ha : a ∈ T) :
      projected a = zero ∨ projected a ∈ inputs := by
    rcases raw a ha with hr | rfl
    · have h := List.all_eq_true.mp base a hr
      simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using h
    · rw [projected_first_or]
      have h := List.all_eq_true.mp base (pin j) (pin_mem j)
      simpa only [Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] using h
  have isZero : observe zero = fun _ => false := by
    funext r
    simp [observe, bit, zero]
  have supplyRoots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows embed)) := by
    intro v hv
    obtain ⟨_, hin, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, hmFront, rfl⟩ := List.mem_map.mp hin
    rw [observe_projected]
    rcases permitted a (eqT ▸ List.mem_toFinset.mpr hmFront) with hz | hm
    · exact Or.inr (Or.inl ⟨false, hz ▸ isZero⟩)
    · exact Or.inl (List.mem_map.mpr ⟨_, hm, rfl⟩)
  have need := projected_bound embed hrun (same ▸ observe_proper graph_proper)
    Reach.start supplyRoots (L := 15) (same ▸ nineFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, isZero⟩
    simp [front, mass_cons, cost, ac]
  omega

lemma first_or_seventeen (j : Fin 10) (hj : j ≠ 0) {k : Nat}
    {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin 1 Extended.first (pin j)) U)) :
    17 ≤ k + 1 := by
  have firstPresent := first_or_retained j hj raw tailRun
  have floor := first_or_tail_sixteen j tailRun
    (Finset.mem_insert_of_mem firstPresent) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (raw a ha))
  omega

end PEqualNP.Outside.Pilot113FirstOr
