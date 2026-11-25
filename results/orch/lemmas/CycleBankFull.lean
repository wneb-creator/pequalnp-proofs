import PEqualNP.Outside.L_meta_2592
namespace PEqualNP.Outside.L_meta_2592.Signed.Extended

def cyclePins : List Sig := ([2,3,8,6,9,7] : List Nat).map (fun i => pins.getD i zero)
def cyclePin (q : Fin 6) : Sig := cyclePins.getD q.val zero
def oppositeBank : List Sig := [bin 1 (cyclePin 0) (cyclePin 3),
  bin 1 (cyclePin 1) (cyclePin 4), bin 1 (cyclePin 2) (cyclePin 5)]
def cycleTarget : Sig := 0xffffffffffc8ffc8ffffffffffc8ffc8ffffffffffc8ffc8ffffffffffc8ffc8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8ffffffffffc8ffc8ffffffffffc8ffc8ffffffffffc8ffc8ffffffffffc8ffc8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8faeafaeaf8c8f8c8

def cycleRows (q : Fin 6) : Row × Row :=
  let weight := ([32,256,8,4,2,1] : List Nat)
  let base := weight.getD ((q.val+3)%6) 0 + weight.getD ((q.val+1)%6) 0
  (Fin.ofNat 1024 base, Fin.ofNat 1024 (base + weight.getD q.val 0))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma cycleChecked : ∀ q : Fin 6,
    let rs := cycleRows q
    bit rs.1 cycleTarget ≠ bit rs.2 cycleTarget ∧
    (∀ p : Fin 6, p ≠ q → bit rs.1 (cyclePin p) = bit rs.2 (cyclePin p)) ∧
    (∀ m : Fin 3, bit rs.1 (oppositeBank.getD m.val zero) =
      bit rs.2 (oppositeBank.getD m.val zero)) := by
  decide +kernel

lemma cyclePin_mem (v : Sig) : v ∈ cyclePins ↔ ∃ q : Fin 6, cyclePin q = v := by
  have pinsEq : cyclePins = List.ofFn cyclePin := by decide +kernel
  rw [pinsEq, List.mem_ofFn]

lemma oppositeBank_mem (v : Sig) : v ∈ oppositeBank ↔
    ∃ m : Fin 3, oppositeBank.getD m.val zero = v := by
  have bankEq : oppositeBank = List.ofFn (fun m : Fin 3 => oppositeBank.getD m.val zero) :=
    by decide +kernel
  conv_lhs => rw [bankEq]
  exact List.mem_ofFn

lemma cycle_bank_keeps_pin (q : Fin 6) {u : Bool} {k : Nat} {S : Finset Sig}
    (raw : ∀ v ∈ S, v ∈ cyclePins ∨ v ∈ oppositeBank)
    (run : Live u cycleTarget k S) : cyclePin q ∈ S := by
  by_contra missing
  obtain ⟨diff, otherPins, bankSame⟩ := cycleChecked q
  obtain ⟨v, hv, changed⟩ := live_row_difference run diff
  rcases raw v hv with pin | bank
  · obtain ⟨p, eq⟩ := (cyclePin_mem v).mp pin
    have pq : p ≠ q := by
      rintro rfl
      exact missing (eq.symm ▸ hv)
    exact changed (eq ▸ otherPins p pq)
  · obtain ⟨m, rfl⟩ := (oppositeBank_mem v).mp bank
    exact changed (bankSame m)

lemma live_card_bound {u T k S} (run : Live u T k S) : S.card ≤ k+1 := by
  induction run using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab fresh tail ih =>
    have absent : bin d a b ∉ U := fun h => fresh (by simp [h])
    rw [Finset.card_insert_of_notMem absent] at ih
    have aStep := Finset.card_insert_le (a := a) (s := insert b U)
    have bStep := Finset.card_insert_le (a := b) (s := U)
    omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma cycleBank_card : ∀ m n : Fin 3, m ≠ n →
    (insert (oppositeBank.getD m.val zero)
      (insert (oppositeBank.getD n.val zero) cyclePins.toFinset)).card = 8 := by
  decide +kernel

lemma two_opposite_bank_floor (m n : Fin 3) (mn : m ≠ n)
    {u : Bool} {k : Nat} {S : Finset Sig}
    (keptM : oppositeBank.getD m.val zero ∈ S)
    (keptN : oppositeBank.getD n.val zero ∈ S)
    (raw : ∀ v ∈ S, v ∈ cyclePins ∨ v ∈ oppositeBank)
    (run : Live u cycleTarget k S) : 7 ≤ k := by
  have allPins : cyclePins.toFinset ⊆ S := by
    intro v hv
    obtain ⟨q, rfl⟩ := (cyclePin_mem v).mp (List.mem_toFinset.mp hv)
    exact cycle_bank_keeps_pin q raw run
  have sub : insert (oppositeBank.getD m.val zero)
      (insert (oppositeBank.getD n.val zero) cyclePins.toFinset) ⊆ S := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact keptM
    · rcases Finset.mem_insert.mp hv with rfl | hv
      · exact keptN
      · exact allPins hv
  have lower := Finset.card_le_card sub
  rw [cycleBank_card m n mn] at lower
  have upper := live_card_bound run
  omega

end PEqualNP.Outside.L_meta_2592.Signed.Extended
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
