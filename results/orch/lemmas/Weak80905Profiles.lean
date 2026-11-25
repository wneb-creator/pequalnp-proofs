import CofactorMoves
import Mono18CanonicalCofactors

namespace PEqualNP.Outside.L_meta_2373.Live1024.Mono18Profiles
open CofactorMoves

def swapRows (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  (a &&& ~~~b, b &&& ~~~a, Fin.ofNat 1024 ((1 <<< j) - (1 <<< i)))

def moves2 : List Move := [(inputs.getD 9 zero, zero, 512), swapRows 65, swapRows 146, swapRows 99]

def domain2 : Sig := ~~~(inputs.getD 2 zero)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice2 {u : Bool} : Slice u inputs graph domain2 15 := by
  exact slice_correct (ms := moves2)
    (base := (NineSigned.vars 511).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target0)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower0))

def moves3 : List Move := [(inputs.getD 9 zero, zero, 512), swapRows 98, swapRows 147, swapRows 135]

def domain3 : Sig := ~~~(inputs.getD 3 zero)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice3 {u : Bool} : Slice u inputs graph domain3 15 := by
  exact slice_correct (ms := moves3)
    (base := (NineSigned.vars 511).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target0)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower0))

def moves10 : List Move := [(~~~(inputs.getD 9 zero), zero, 512), swapRows 144, swapRows 65, swapRows 146, swapRows 67, swapRows 100, swapRows 117, swapRows 152]

def domain10 : Sig := inputs.getD 0 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice10 {u : Bool} : Slice u inputs graph domain10 11 := by
  exact slice_correct (ms := moves10)
    (base := (NineSigned.vars 511).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target1)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower1))

def moves11 : List Move := [(~~~(inputs.getD 9 zero), zero, 512), swapRows 96, swapRows 145, swapRows 66, swapRows 99, swapRows 148, swapRows 133, swapRows 118]

def domain11 : Sig := inputs.getD 1 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice11 {u : Bool} : Slice u inputs graph domain11 11 := by
  exact slice_correct (ms := moves11)
    (base := (NineSigned.vars 511).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target1)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower1))

def moves16 : List Move := [(~~~(inputs.getD 9 zero), zero, 512), swapRows 65, swapRows 50, swapRows 150, swapRows 135]

def domain16 : Sig := inputs.getD 6 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice16 {u : Bool} : Slice u inputs graph domain16 11 := by
  exact slice_correct (ms := moves16)
    (base := (NineSigned.vars 511).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target1)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower1))

def moves41 : List Move := [(inputs.getD 4 zero, zero, 1008), (inputs.getD 9 zero, zero, 512), swapRows 16, swapRows 66, swapRows 101, swapRows 151]

def domain41 : Sig := ~~~(inputs.getD 2 zero) &&& ~~~(inputs.getD 7 zero)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice41 {u : Bool} : Slice u inputs graph domain41 13 := by
  exact slice_correct (ms := moves41)
    (base := (NineSigned.vars 495).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target2)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower2))

def moves74 : List Move := [(inputs.getD 4 zero, zero, 1008), (~~~(inputs.getD 9 zero), zero, 512), swapRows 144, swapRows 97, swapRows 98, swapRows 147, swapRows 117, swapRows 134, swapRows 135]

def domain74 : Sig := ~~~(inputs.getD 4 zero) &&& inputs.getD 0 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice74 {u : Bool} : Slice u inputs graph domain74 10 := by
  exact slice_correct (ms := moves74)
    (base := (NineSigned.vars 495).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target4)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower4))

def moves76 : List Move := [(inputs.getD 4 zero, zero, 1008), (~~~(inputs.getD 9 zero), zero, 512), swapRows 144, swapRows 97, swapRows 98, swapRows 99, swapRows 116, swapRows 117, swapRows 134, swapRows 151]

def domain76 : Sig := ~~~(inputs.getD 5 zero) &&& inputs.getD 0 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice76 {u : Bool} : Slice u inputs graph domain76 10 := by
  exact slice_correct (ms := moves76)
    (base := (NineSigned.vars 495).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target4)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower4))

def moves174 : List Move := [(inputs.getD 4 zero, zero, 1008), (~~~(inputs.getD 9 zero), zero, 512), swapRows 128, swapRows 97, swapRows 98, swapRows 131, swapRows 84, swapRows 133, swapRows 150, swapRows 151]

def domain174 : Sig := ~~~(inputs.getD 8 zero) &&& inputs.getD 6 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice174 {u : Bool} : Slice u inputs graph domain174 10 := by
  exact slice_correct (ms := moves174)
    (base := (NineSigned.vars 495).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target4)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower4))

def moves176 : List Move := [(inputs.getD 4 zero, zero, 1008), (~~~(inputs.getD 9 zero), zero, 512), swapRows 16, swapRows 97, swapRows 130, swapRows 83, swapRows 100, swapRows 133, swapRows 150, swapRows 135]

def domain176 : Sig := ~~~(inputs.getD 9 zero) &&& inputs.getD 6 zero

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma slice176 {u : Bool} : Slice u inputs graph domain176 10 := by
  exact slice_correct (ms := moves176)
    (base := (NineSigned.vars 495).map sliceNineLift)
    (G := sliceNineLift NineSigned.Mono18Cofactors.target4)
    (by decide +kernel) (by decide +kernel) (by unfold proper; decide +kernel)
    (lower_lift (NineSigned.lower_mode_of_signed NineSigned.Mono18Cofactors.lower4))

end PEqualNP.Outside.L_meta_2373.Live1024.Mono18Profiles
