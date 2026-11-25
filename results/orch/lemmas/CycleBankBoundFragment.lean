namespace PEqualNP.Outside.L_meta_2592.Signed

lemma cycle_run_with_signs {R u} {goal : Wire R} {k xs} (run : Run u goal k xs) :
    Run true goal k xs := by
  induction run using Run.ind with
  | stop => exact Run.stop
  | perm p h ih => exact Run.perm p ih
  | two op hd ka kb h ih =>
    apply Run.two op ?_ ka kb ih
    rcases hd with low | ⟨hu, high⟩
    · exact Or.inl low
    · exact Or.inr ⟨rfl, high⟩

def cycleLabels : List Nat := [0,4,3,2,7,5]
def cycleProjection (r : Row) : Extended.Row := Fin.ofNat 1024
  (((List.range 6).map (fun q =>
    if r.val.testBit (cycleLabels.getD q 0) then
      ([32,256,8,4,2,1] : List Nat).getD q 0 else 0)).sum)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma cycleProjectionChecked : ∀ r : Row,
    Extended.bit (cycleProjection r) Extended.cycleTarget = bit r (graphGoal 189) ∧
    ∀ q : Fin 6, Extended.bit (cycleProjection r) (Extended.cyclePin q) =
      bit r (inputs.getD (cycleLabels.getD q.val 0) zero) := by
  decide +kernel

lemma cycle_projection_target : restrictRows cycleProjection (Extended.observe Extended.cycleTarget) =
    observe (graphGoal 189) := by
  funext r
  exact (cycleProjectionChecked r).1

lemma cycle_projection_supply (v : Extended.Sig) (hv : v ∈ Extended.cyclePins) :
    Available true ((vars 189).map observe)
      (restrictRows cycleProjection (Extended.observe v)) := by
  obtain ⟨q, rfl⟩ := (Extended.cyclePin_mem v).mp hv
  have mem : inputs.getD (cycleLabels.getD q.val 0) zero ∈ vars 189 := by
    revert q
    decide +kernel
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨inputs.getD (cycleLabels.getD q.val 0) zero, mem, ?_⟩
  funext r
  exact (cycleProjectionChecked r).2 q |>.symm

lemma cycle_one_bank_floor (m : Fin 3) {u : Bool} {k : Nat} {S : Finset Extended.Sig}
    (raw : ∀ v ∈ S, v ∈ Extended.cyclePins ∨
      v = Extended.oppositeBank.getD m.val Extended.zero)
    (run : Extended.Live u Extended.cycleTarget k S) : 7 ≤ k := by
  classical
  let left : Fin 6 := ⟨m.val, by omega⟩
  let right : Fin 6 := ⟨m.val+3, by omega⟩
  let projected := restrictRows cycleProjection
    (Extended.observe (Extended.oppositeBank.getD m.val Extended.zero))
  have leftMem : Extended.cyclePin left ∈ Extended.cyclePins :=
    (Extended.cyclePin_mem _).mpr ⟨left, rfl⟩
  have rightMem : Extended.cyclePin right ∈ Extended.cyclePins :=
    (Extended.cyclePin_mem _).mpr ⟨right, rfl⟩
  have bankEq : Extended.oppositeBank.getD m.val Extended.zero =
      Extended.bin 1 (Extended.cyclePin left) (Extended.cyclePin right) := by
    fin_cases m <;> rfl
  have reach : Reach true ((vars 189).map observe) 1
      (projected :: (vars 189).map observe) := by
    have step := Reach.two true Reach.start
      (cycle_projection_supply _ leftMem) (cycle_projection_supply _ rightMem)
    change Reach true ((vars 189).map observe) 1
      (restrictRows cycleProjection
        (Extended.observe (Extended.oppositeBank.getD m.val Extended.zero)) :: _)
    rw [bankEq, Extended.obs_bin, restrict_comb]
    exact step
  have listRun := Extended.list_run run S.toList (Finset.nodup_toList S) (by simp)
  have signedRun : Run true (Extended.observe Extended.cycleTarget) k
      (S.toList.map Extended.observe) := by
    exact cycle_run_with_signs listRun
  have supplied : supply true (projected :: (vars 189).map observe)
      ((S.toList.map Extended.observe).map (restrictRows cycleProjection)) := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hw
    rcases raw z (Finset.mem_toList.mp hz) with pin | rfl
    · exact available_cons projected (cycle_projection_supply z pin)
    · exact Or.inl List.mem_cons_self
  have graphProper : proper (graphGoal 189) := by unfold proper; decide +kernel
  have bound := projected_bound cycleProjection signedRun
    (cycle_projection_target ▸ observe_proper graphProper) reach supplied
    (L := 8) (cycle_projection_target ▸ low189)
  omega

lemma cycle_bank_floor {u : Bool} {k : Nat} {S : Finset Extended.Sig}
    (raw : ∀ v ∈ S, v ∈ Extended.cyclePins ∨ v ∈ Extended.oppositeBank)
    (run : Extended.Live u Extended.cycleTarget k S) : 7 ≤ k := by
  by_cases h0 : Extended.oppositeBank.getD 0 Extended.zero ∈ S
  · by_cases h1 : Extended.oppositeBank.getD 1 Extended.zero ∈ S
    · exact Extended.two_opposite_bank_floor 0 1 (by decide) h0 h1 raw run
    · by_cases h2 : Extended.oppositeBank.getD 2 Extended.zero ∈ S
      · exact Extended.two_opposite_bank_floor 0 2 (by decide) h0 h2 raw run
      · apply cycle_one_bank_floor 0 ?_ run
        intro v hv
        rcases raw v hv with pin | bank
        · exact Or.inl pin
        · simp only [Extended.oppositeBank, List.mem_cons, List.not_mem_nil, or_false] at bank
          rcases bank with rfl | rfl | rfl
          · exact Or.inr rfl
          · exact False.elim (h1 hv)
          · exact False.elim (h2 hv)
  · by_cases h1 : Extended.oppositeBank.getD 1 Extended.zero ∈ S
    · by_cases h2 : Extended.oppositeBank.getD 2 Extended.zero ∈ S
      · exact Extended.two_opposite_bank_floor 1 2 (by decide) h1 h2 raw run
      · apply cycle_one_bank_floor 1 ?_ run
        intro v hv
        rcases raw v hv with pin | bank
        · exact Or.inl pin
        · simp only [Extended.oppositeBank, List.mem_cons, List.not_mem_nil, or_false] at bank
          rcases bank with rfl | rfl | rfl
          · exact False.elim (h0 hv)
          · exact Or.inr rfl
          · exact False.elim (h2 hv)
    · apply cycle_one_bank_floor 2 ?_ run
      intro v hv
      rcases raw v hv with pin | bank
      · exact Or.inl pin
      · simp only [Extended.oppositeBank, List.mem_cons, List.not_mem_nil, or_false] at bank
        rcases bank with rfl | rfl | rfl
        · exact False.elim (h0 hv)
        · exact False.elim (h1 hv)
        · exact Or.inr rfl

end PEqualNP.Outside.L_meta_2592.Signed
