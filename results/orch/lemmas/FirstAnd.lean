import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113FirstAnd

open PEqualNP.Outside.L_meta_6581

abbrev pin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

def gateOp (signed : Bool) : ℕ := if signed then 2 else 0

def witnessRow (signed : Bool) (j : Fin 10) : Extended.Row :=
  if signed then ![0, 192, 96, 384, 192, 144, 68, 129, 136, 130] j
  else if j = 5 then 64 else 16

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
lemma witness_data : ∀ (signed : Bool) (j : Fin 10), j ≠ 0 →
    Extended.bit (witnessRow signed j) Extended.target ≠
      Extended.bit (witnessRow signed j + 512) Extended.target ∧
    Extended.bit (witnessRow signed j)
        (Extended.bin (gateOp signed) Extended.first (pin j)) =
      Extended.bit (witnessRow signed j + 512)
        (Extended.bin (gateOp signed) Extended.first (pin j)) ∧
    Extended.initial.all (fun a => (a == Extended.first) ||
      (Extended.bit (witnessRow signed j) a ==
        Extended.bit (witnessRow signed j + 512) a)) = true ∧
    Extended.bin (gateOp signed) Extended.first (pin j) ≠ Extended.first := by
  decide +kernel

lemma first_and_retained (signed : Bool) (j : Fin 10) (hj : j ≠ 0)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin (gateOp signed) Extended.first (pin j)) U)) :
    Extended.first ∈ U := by
  obtain ⟨different, same, onlyFirst, _⟩ := witness_data signed j hj
  obtain ⟨a, ha, changes⟩ := Extended.live_row_difference tailRun different
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact False.elim (changes same)
  · have h := List.all_eq_true.mp onlyFirst a (raw a ha)
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    exact h.resolve_right changes ▸ ha

lemma projected_first_and (signed : Bool) (j : Fin 10) :
    projected (Extended.bin (gateOp signed) Extended.first (pin j)) = zero := by
  have hz : Extended.first.setWidth 512 = (0 : BitVec 512) := by decide +kernel
  cases signed <;>
    change (Extended.first &&& _).setWidth 512 = (0 : BitVec 512)
  all_goals
    rw [BitVec.setWidth_and, hz]
    simp

lemma first_and_tail_seventeen (signed : Bool) (j : Fin 10) (hj : j ≠ 0)
    {k : ℕ} {T : Finset Extended.Sig}
    (tailRun : Extended.Live true Extended.target k T)
    (firstPresent : Extended.first ∈ T)
    (andPresent : Extended.bin (gateOp signed) Extended.first (pin j) ∈ T)
    (raw : ∀ a ∈ T, a ∈ Extended.initial ∨
      a = Extended.bin (gateOp signed) Extended.first (pin j)) :
    17 ≤ k := by
  classical
  let gate := Extended.bin (gateOp signed) Extended.first (pin j)
  have distinct : gate ≠ Extended.first := (witness_data signed j hj).2.2.2
  have gatePresent : gate ∈ T := andPresent
  let front := Extended.first :: gate :: ((T.erase Extended.first).erase gate).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, List.nodup_cons.mpr ⟨?_, Finset.nodup_toList _⟩⟩
    · simp [ne_comm.mp distinct]
    · simp
  have eqT : front.toFinset = T := by
    ext a
    by_cases ha : a = Extended.first <;> by_cases hb : a = gate <;>
      simp [front, ha, hb, firstPresent, gatePresent]
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
    · exact Or.inl (projected_first_and signed j)
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
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows embed)) := by
    have ac : Constant (restrictRows embed (Extended.observe Extended.first)) := by
      rw [observe_projected, show projected Extended.first = zero by decide +kernel]
      exact ⟨false, isZero⟩
    have bc : Constant (restrictRows embed (Extended.observe gate)) := by
      rw [observe_projected, projected_first_and signed j]
      exact ⟨false, isZero⟩
    simp [front, mass_cons, cost, ac, bc]
    omega
  omega

lemma first_and_eighteen (signed : Bool) (j : Fin 10) (hj : j ≠ 0)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (tailRun : Extended.Live true Extended.target k
      (insert (Extended.bin (gateOp signed) Extended.first (pin j)) U)) :
    18 ≤ k + 1 := by
  have firstPresent := first_and_retained signed j hj raw tailRun
  have floor := first_and_tail_seventeen signed j hj tailRun
    (Finset.mem_insert_of_mem firstPresent) (Finset.mem_insert_self _ _) (by
      intro a ha
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact Or.inr rfl
      · exact Or.inl (raw a ha))
  omega

end PEqualNP.Outside.Pilot113FirstAnd
