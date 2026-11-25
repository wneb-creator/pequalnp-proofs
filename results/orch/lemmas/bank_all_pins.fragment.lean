namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.CanonicalBank

def pinWitness (d : Fin 4) (j : Fin 2) (i : Fin 10) : Extended.Row :=
  (![![![16, 4, 1, 8, 2, 1, 2, 2, 4, 1], ![16, 4, 1, 8, 2, 1, 2, 2, 4, 1]], ![![128, 512, 1, 8, 2, 1, 2, 2, 4, 1], ![48, 4, 513, 8, 2, 1, 2, 2, 4, 1]], ![![128, 4, 1, 8, 2, 1, 2, 2, 4, 1], ![48, 4, 1, 8, 2, 1, 2, 2, 4, 1]], ![![16, 512, 1, 8, 2, 1, 2, 2, 4, 1], ![16, 4, 513, 8, 2, 1, 2, 2, 4, 1]]]) d j i

def pinOther (d : Fin 4) (j : Fin 2) (i : Fin 10) : Extended.Row :=
  Fin.ofNat 1024 ((pinWitness d j i).val + 2 ^ (![9,7,5,8,6,4,2,0,3,1] i : Nat))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_target_diff : ∀ d : Fin 4, ∀ j : Fin 2, ∀ i : Fin 10,
    Extended.bit (pinWitness d j i) Extended.target ≠
      Extended.bit (pinOther d j i) Extended.target := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma pin_other_stable : ∀ d : Fin 4, ∀ j : Fin 2, ∀ i : Fin 10,
    (bank d j).all (fun a =>
      (Extended.bit (pinWitness d j i) a == Extended.bit (pinOther d j i) a) ||
      (a == Extended.pins.getD i.val Extended.zero)) = true := by
  decide +kernel

lemma pin_needed (d : Fin 4) (j : Fin 2) (i : Fin 10) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) : Extended.pins.getD i.val Extended.zero ∈ S := by
  obtain ⟨a,ha,hchange⟩ := Extended.live_row_difference run (pin_target_diff d j i)
  have chk := List.all_eq_true.mp (pin_other_stable d j i) a (raw a ha)
  simp only [Bool.or_eq_true,beq_iff_eq] at chk
  exact chk.resolve_left hchange ▸ ha

lemma all_pins_needed (d : Fin 4) (j : Fin 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) : Extended.pins.toFinset ⊆ S := by
  intro a ha
  have hlist : List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) = Extended.pins := rfl
  have hm := List.mem_toFinset.mp ha
  rw [←hlist] at hm
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hm
  exact pin_needed d j i run raw

lemma exact_bank (d : Fin 4) (j : Fin 2) {k S}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ bank d j) (used : extra d j ∈ S) :
    S = (bank d j).toFinset := by
  apply Finset.Subset.antisymm
  · intro a ha
    exact List.mem_toFinset.mpr (raw a ha)
  · intro a ha
    have hm := List.mem_toFinset.mp ha
    simp only [bank,List.mem_append,List.mem_singleton] at hm
    rcases hm with hp | rfl
    · exact all_pins_needed d j run raw (List.mem_toFinset.mpr hp)
    · exact used

end PEqualNP.Outside.L_meta_2592_aux.Stronger.CanonicalBank
