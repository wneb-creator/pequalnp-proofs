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
