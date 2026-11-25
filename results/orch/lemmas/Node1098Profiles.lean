import SliceProfiles

namespace PEqualNP.Outside.L_meta_2373.NineSigned

def positiveDoubleZero : Sig := graphGoal 431 ||| inputs.getD 7 zero

def positiveDoubleZeroWitnesses : List (Sig × Row × Row) := [(inputs.getD 7 zero, 0, 128)]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zeroTwo_lower13 : Lower true (vars 495) (graphGoal 495) 13 := by
  have h := valid383 (495, 13) (by decide +kernel)
  simpa only [varsX, show (495 : Nat) < 512 from by decide, ite_true] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma zeroThree_lower11 : Lower true (vars 431) (graphGoal 431) 11 := by
  have h := valid191 (431, 11) (by decide +kernel)
  simpa only [varsX, show (431 : Nat) < 512 from by decide, ite_true] using h

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma positiveDoubleZero_lower9 : Lower true (vars 431) positiveDoubleZero 9 := by
  have h := lift_ok (u := true) (ms := zeroPositiveMoves)
    (T := positiveDoubleZero) (raw := vars 431) (base := vars 303)
    (G := graphGoal 303) (xs := positiveDoubleZeroWitnesses) (L := 8)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) cofactor_cycle_lower8
  have count : (positiveDoubleZeroWitnesses.map Prod.fst).toFinset.card = 1 := by decide +kernel
  simpa only [count] using h

end PEqualNP.Outside.L_meta_2373.NineSigned

namespace PEqualNP.Outside.L_meta_2373.Live1024.Node1098Profiles

def permutation (c : Fin 9) : Fin 10 → Fin 10 :=
  ![![3, 4, 9, 7, 2, 8, 0, 6, 5, 1], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1], ![2, 3, 8, 6, 1, 7, 4, 5, 9, 0], ![4, 3, 8, 5, 0, 9, 2, 6, 7, 1], ![4, 0, 5, 8, 3, 9, 1, 7, 6, 2], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![3, 8, 5, 7, 2, 4, 6, 0, 9, 1], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]] c

def inverse (c : Fin 9) : Fin 10 → Fin 10 :=
  ![![6, 9, 4, 0, 1, 8, 7, 3, 5, 2], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![6, 9, 4, 0, 1, 8, 7, 3, 5, 2], ![9, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5], ![1, 6, 9, 4, 0, 2, 8, 7, 3, 5], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![7, 9, 4, 0, 5, 2, 6, 3, 1, 8], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2]] c

def mask (c : Fin 9) : Nat := ![511, 511, 511, 495, 495, 495, 431, 431, 431] c

def positive (c : Fin 9) : Bool := ![false, false, true, false, true, true, false, false, true] c

def bound (c : Fin 9) : Nat := ![15, 15, 11, 13, 10, 10, 11, 11, 9] c

def rows (c : Fin 9) (r : NineSigned.Row) : Row :=
  Fin.ofNat 1024 ((if positive c then 2 ^ (permutation c 9).val else 0) +
    ∑ i : Fin 9, if (mask c).testBit i.val && r.val.testBit i.val then
      2 ^ (permutation c i.castSucc).val else 0)

def domain (c : Fin 9) : Sig := ![(~~~(inputs.getD 1 zero)), (~~~(inputs.getD 3 zero)), (inputs.getD 1 zero), (~~~(inputs.getD 0 zero) &&& ~~~(inputs.getD 1 zero)), (~~~(inputs.getD 0 zero) &&& inputs.getD 1 zero), (~~~(inputs.getD 3 zero) &&& inputs.getD 2 zero), (~~~(inputs.getD 1 zero) &&& ~~~(inputs.getD 2 zero) &&& ~~~(inputs.getD 3 zero)), (~~~(inputs.getD 1 zero) &&& ~~~(inputs.getD 2 zero) &&& ~~~(inputs.getD 6 zero)), (~~~(inputs.getD 1 zero) &&& ~~~(inputs.getD 3 zero) &&& inputs.getD 2 zero)] c

def target (c : Fin 9) : NineSigned.Sig := ![NineSigned.graph, NineSigned.graph, NineSigned.positiveNine, NineSigned.graphGoal 495, NineSigned.positiveAdjacentZero, NineSigned.positiveAdjacentZero, NineSigned.graphGoal 431, NineSigned.graphGoal 431, NineSigned.positiveDoubleZero] c

def roots (c : Fin 9) : List NineSigned.Sig := ![NineSigned.inputs, NineSigned.inputs, NineSigned.positiveNineRaw, NineSigned.vars 495, NineSigned.positiveAdjacentZeroRaw, NineSigned.positiveAdjacentZeroRaw, NineSigned.vars 431, NineSigned.vars 431, NineSigned.vars 431] c

def inputMap (c : Fin 9) (i : Fin 10) : NineSigned.Sig :=
  if inverse c i = 9 then (if positive c then NineSigned.one else NineSigned.zero)
  else if (mask c).testBit (inverse c i).val then
    NineSigned.inputs.getD (inverse c i).val NineSigned.zero
  else NineSigned.zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma rows_domain : ∀ (c : Fin 9) (r : NineSigned.Row), bit (rows c r) (domain c) = true := by
  intro c
  fin_cases c <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma rows_goal : ∀ (c : Fin 9) (r : NineSigned.Row), observe graph (rows c r) = NineSigned.observe (target c) r := by
  intro c
  fin_cases c <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma rows_input : ∀ (c : Fin 9) (i : Fin 10) (r : NineSigned.Row),
    observe (inputs.getD i.val zero) (rows c r) = NineSigned.observe (inputMap c i) r := by
  intro c i
  fin_cases c <;> fin_cases i <;> decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma inputMap_free : ∀ (c : Fin 9) (i : Fin 10), NineSigned.freeWord (roots c) (inputMap c i) = true := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma target_proper : ∀ c : Fin 9, NineSigned.proper (target c) := by
  unfold NineSigned.proper
  decide +kernel

lemma rows_available {u : Bool} (c : Fin 9) (i : Fin 10) :
    NineSigned.Available u ((roots c).map NineSigned.observe)
      (restrictRows (rows c) (observe (inputs.getD i.val zero))) := by
  have heq : restrictRows (rows c) (observe (inputs.getD i.val zero)) =
      NineSigned.observe (inputMap c i) := by
    funext r
    exact rows_input c i r
  rw [heq]
  exact NineSigned.freeWord_ok (inputMap_free c i)

lemma target_lower {u : Bool} (c : Fin 9) :
    NineSigned.Lower u (roots c) (target c) (bound c) := by
  fin_cases c
  · exact NineSigned.lower_mode_of_signed NineSigned.nine_reach_lower
  · exact NineSigned.lower_mode_of_signed NineSigned.nine_reach_lower
  · exact NineSigned.lower_mode_of_signed NineSigned.positiveNine_lower11
  · exact NineSigned.lower_mode_of_signed NineSigned.zeroTwo_lower13
  · exact NineSigned.lower_mode_of_signed NineSigned.positiveAdjacentZero_lower10
  · exact NineSigned.lower_mode_of_signed NineSigned.positiveAdjacentZero_lower10
  · exact NineSigned.lower_mode_of_signed NineSigned.zeroThree_lower11
  · exact NineSigned.lower_mode_of_signed NineSigned.zeroThree_lower11
  · exact NineSigned.lower_mode_of_signed NineSigned.positiveDoubleZero_lower9

lemma slice {u : Bool} (c : Fin 9) : Slice u inputs graph (domain c) (bound c) := by
  apply Slice_from_nine (rows c) inputs graph (domain c) (roots c) (target c) (bound c)
  · exact rows_domain c
  · funext r
    exact rows_goal c r
  · intro a ha
    rw [← input_list] at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact rows_available c i
  · exact target_proper c
  · exact target_lower c

end PEqualNP.Outside.L_meta_2373.Live1024.Node1098Profiles
