import SliceProfiles

namespace PEqualNP.Outside.L_meta_2373.NineSigned.Mono18Cofactors

def target0 : Sig := graphGoal 511

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower0 : Lower true (vars 511) target0 15 := by
  rw [show vars 511 = inputs from by decide +kernel,
    show target0 = graph from by decide +kernel]
  exact nine_reach_lower

def target1 : Sig := graphGoal 511 ||| inputs.getD 4 zero ||| inputs.getD 6 zero ||| inputs.getD 7 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower1 : Lower true (vars 511) target1 11 := by
  have base : Lower true (vars 303) (graphGoal 303) 8 := by
    have h := valid189 (303, 8) (by decide +kernel)
    simpa only [varsX, show (303 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 4 zero, zero, 496), (inputs.getD 6 zero, zero, 448), (inputs.getD 7 zero, zero, 384)])
    (T := target1) (raw := vars 511) (base := vars 303)
    (G := graphGoal 303) (xs := [(inputs.getD 4 zero, 0, 16), (inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)]) (L := 8)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 4 zero, 0, 16), (inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by decide +kernel
  simpa only [card] using lifted

def target2 : Sig := graphGoal 495

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower2 : Lower true (vars 495) target2 13 := by
  have base : Lower true (vars 495) (graphGoal 495) 13 := by
    have h := valid383 (495, 13) (by decide +kernel)
    simpa only [varsX, show (495 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target3 : Sig := graphGoal 509

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower3 : Lower true (vars 509) target3 12 := by
  have base : Lower true (vars 509) (graphGoal 509) 12 := by
    have h := valid255 (509, 12) (by decide +kernel)
    simpa only [varsX, show (509 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target4 : Sig := graphGoal 495 ||| inputs.getD 6 zero ||| inputs.getD 7 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower4 : Lower true (vars 495) target4 10 := by
  have base : Lower true (vars 303) (graphGoal 303) 8 := by
    have h := valid189 (303, 8) (by decide +kernel)
    simpa only [varsX, show (303 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 6 zero, zero, 448), (inputs.getD 7 zero, zero, 384)])
    (T := target4) (raw := vars 495) (base := vars 303)
    (G := graphGoal 303) (xs := [(inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)]) (L := 8)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  simpa only [card] using lifted

def target5 : Sig := graphGoal 503 ||| inputs.getD 2 zero ||| inputs.getD 4 zero ||| inputs.getD 8 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower5 : Lower true (vars 503) target5 8 := by
  have base : Lower true (vars 227) (graphGoal 227) 5 := by
    have h := valid47 (227, 5) (by decide +kernel)
    simpa only [varsX, show (227 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 2 zero, zero, 508), (inputs.getD 4 zero, zero, 496), (inputs.getD 8 zero, zero, 256)])
    (T := target5) (raw := vars 503) (base := vars 227)
    (G := graphGoal 227) (xs := [(inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 8 zero, 0, 256)]) (L := 5)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 2 zero, 0, 4), (inputs.getD 4 zero, 0, 16), (inputs.getD 8 zero, 0, 256)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by decide +kernel
  simpa only [card] using lifted

def target6 : Sig := graphGoal 494

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower6 : Lower true (vars 494) target6 11 := by
  have base : Lower true (vars 494) (graphGoal 494) 11 := by
    have h := valid191 (494, 11) (by decide +kernel)
    simpa only [varsX, show (494 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target7 : Sig := graphGoal 508

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower7 : Lower true (vars 508) target7 9 := by
  have base : Lower true (vars 508) (graphGoal 508) 9 := by
    have h := valid127 (508, 9) (by decide +kernel)
    simpa only [varsX, show (508 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target8 : Sig := graphGoal 502

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower8 : Lower true (vars 502) target8 8 := by
  have base : Lower true (vars 486) (graphGoal 486) 8 := by
    have h := valid189 (486, 8) (by decide +kernel)
    simpa only [varsX, show (486 : Nat) < 512 from by decide, ite_true] using h
  exact lower_map (ms := [(inputs.getD 4 zero, zero, 496)])
    (raw := vars 502) (T := target8) (base := vars 486) (G := graphGoal 486)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel) base

def target9 : Sig := graphGoal 251

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower9 : Lower true (vars 251) target9 8 := by
  have base : Lower true (vars 251) (graphGoal 251) 8 := by
    have h := valid251 (251, 8) (by decide +kernel)
    simpa only [varsX, show (251 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target10 : Sig := graphGoal 431 ||| inputs.getD 7 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower10 : Lower true (vars 431) target10 9 := by
  have base : Lower true (vars 303) (graphGoal 303) 8 := by
    have h := valid189 (303, 8) (by decide +kernel)
    simpa only [varsX, show (303 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 7 zero, zero, 384)])
    (T := target10) (raw := vars 431) (base := vars 303)
    (G := graphGoal 303) (xs := [(inputs.getD 7 zero, 0, 128)]) (L := 8)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 7 zero, 0, 128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 1 := by decide +kernel
  simpa only [card] using lifted

def target11 : Sig := graphGoal 478 ||| inputs.getD 7 zero ||| inputs.getD 8 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower11 : Lower true (vars 478) target11 7 := by
  have base : Lower true (vars 94) (graphGoal 94) 5 := by
    have h := valid47 (94, 5) (by decide +kernel)
    simpa only [varsX, show (94 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 7 zero, zero, 384), (inputs.getD 8 zero, zero, 256)])
    (T := target11) (raw := vars 478) (base := vars 94)
    (G := graphGoal 94) (xs := [(inputs.getD 7 zero, 0, 128), (inputs.getD 8 zero, 0, 256)]) (L := 5)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 7 zero, 0, 128), (inputs.getD 8 zero, 0, 256)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  simpa only [card] using lifted

def target12 : Sig := graphGoal 508 ||| inputs.getD 4 zero ||| inputs.getD 6 zero ||| inputs.getD 7 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower12 : Lower true (vars 508) target12 7 := by
  have base : Lower true (vars 300) (graphGoal 300) 4 := by
    have h := valid15 (300, 4) (by decide +kernel)
    simpa only [varsX, show (300 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 4 zero, zero, 496), (inputs.getD 6 zero, zero, 448), (inputs.getD 7 zero, zero, 384)])
    (T := target12) (raw := vars 508) (base := vars 300)
    (G := graphGoal 300) (xs := [(inputs.getD 4 zero, 0, 16), (inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)]) (L := 4)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 4 zero, 0, 16), (inputs.getD 6 zero, 0, 64), (inputs.getD 7 zero, 0, 128)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 3 := by decide +kernel
  simpa only [card] using lifted

def target13 : Sig := graphGoal 487 ||| inputs.getD 2 zero ||| inputs.getD 8 zero

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower13 : Lower true (vars 487) target13 7 := by
  have base : Lower true (vars 227) (graphGoal 227) 5 := by
    have h := valid47 (227, 5) (by decide +kernel)
    simpa only [varsX, show (227 : Nat) < 512 from by decide, ite_true] using h
  have lifted := lift_ok (u := true) (ms := [(inputs.getD 2 zero, zero, 508), (inputs.getD 8 zero, zero, 256)])
    (T := target13) (raw := vars 487) (base := vars 227)
    (G := graphGoal 227) (xs := [(inputs.getD 2 zero, 0, 4), (inputs.getD 8 zero, 0, 256)]) (L := 5)
    (by decide +kernel) (by unfold proper; decide +kernel)
    (by unfold proper; decide +kernel) base
  have card : (([(inputs.getD 2 zero, 0, 4), (inputs.getD 8 zero, 0, 256)] : List (Sig × Row × Row)).map Prod.fst).toFinset.card = 2 := by decide +kernel
  simpa only [card] using lifted

def target14 : Sig := graphGoal 492

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower14 : Lower true (vars 492) target14 8 := by
  have base : Lower true (vars 492) (graphGoal 492) 8 := by
    have h := valid63 (492, 8) (by decide +kernel)
    simpa only [varsX, show (492 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target15 : Sig := graphGoal 486

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower15 : Lower true (vars 486) target15 8 := by
  have base : Lower true (vars 486) (graphGoal 486) 8 := by
    have h := valid189 (486, 8) (by decide +kernel)
    simpa only [varsX, show (486 : Nat) < 512 from by decide, ite_true] using h
  exact base

def target16 : Sig := graphGoal 504

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma lower16 : Lower true (vars 504) target16 7 := by
  have base : Lower true (vars 504) (graphGoal 504) 7 := by
    have h := valid111 (504, 7) (by decide +kernel)
    simpa only [varsX, show (504 : Nat) < 512 from by decide, ite_true] using h
  exact base

def zeroMask (i : Fin 17) : Nat := ![512, 0, 528, 514, 16, 512, 529, 515, 521, 772, 80, 513, 3, 528, 531, 537, 519] i
def oneMask (i : Fin 17) : Nat := ![0, 512, 0, 0, 512, 8, 0, 0, 0, 0, 512, 32, 512, 8, 0, 0, 0] i
def freeMask (i : Fin 17) : Nat := ![511, 511, 495, 509, 495, 503, 494, 508, 502, 251, 431, 478, 508, 487, 492, 486, 504] i
def target (i : Fin 17) : Sig := ![target0, target1, target2, target3, target4, target5, target6, target7, target8, target9, target10, target11, target12, target13, target14, target15, target16] i
def bound (i : Fin 17) : Nat := ![15, 11, 13, 12, 10, 8, 11, 9, 8, 8, 9, 7, 7, 7, 8, 8, 7] i

lemma lower (i : Fin 17) {u : Bool} : Lower u (vars (freeMask i)) (target i) (bound i) := by
  fin_cases i
  · exact lower_mode_of_signed lower0
  · exact lower_mode_of_signed lower1
  · exact lower_mode_of_signed lower2
  · exact lower_mode_of_signed lower3
  · exact lower_mode_of_signed lower4
  · exact lower_mode_of_signed lower5
  · exact lower_mode_of_signed lower6
  · exact lower_mode_of_signed lower7
  · exact lower_mode_of_signed lower8
  · exact lower_mode_of_signed lower9
  · exact lower_mode_of_signed lower10
  · exact lower_mode_of_signed lower11
  · exact lower_mode_of_signed lower12
  · exact lower_mode_of_signed lower13
  · exact lower_mode_of_signed lower14
  · exact lower_mode_of_signed lower15
  · exact lower_mode_of_signed lower16

end PEqualNP.Outside.L_meta_2373.NineSigned.Mono18Cofactors
