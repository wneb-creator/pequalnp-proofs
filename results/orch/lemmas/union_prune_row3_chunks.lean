import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_2592

def starMasks : List Nat := [22, 37, 25, 42]

def singletonMasks : List Nat := [1, 2, 4, 8, 16, 32]

def helperMasks : List Nat :=
  [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

lemma helperMasks_spec : helperMasks =
    (List.range 64).filter (fun x =>
      x != 0 && Nat.land x (x - 1) != 0 && !(starMasks.contains x)) := by
  decide +kernel

def setStepAllowed (known : List Nat) (target : Nat) : Bool :=
  known.any fun a => Nat.land target a == target ||
    known.any fun b => Nat.lor a b == target

def closeStarStep (known : List Nat) (target : Nat) : List Nat :=
  if known.contains target then known
  else if setStepAllowed known target then target :: known else known

def closeStarSets : Nat → List Nat → List Nat → List Nat
  | 0, _, known => known
  | fuel + 1, allowed, known =>
    let next := allowed.foldl closeStarStep known
    if next.length == known.length then known
    else closeStarSets fuel allowed next

def starTripleSucceeds (a b c : Nat) : Bool :=
  let known := closeStarSets 7 (starMasks ++ [a, b, c]) singletonMasks
  starMasks.all known.contains

def starHelperPair (a b : Nat) : Bool :=
  helperMasks.any fun c => if b < c then starTripleSucceeds a b c else false

def starHelperRow (a : Nat) : Bool :=
  helperMasks.any fun b => if a < b then starHelperPair a b else false

def starHelperSearch : Bool := helperMasks.any starHelperRow

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_5 : starHelperPair 3 5 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_6 : starHelperPair 3 6 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_7 : starHelperPair 3 7 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_9 : starHelperPair 3 9 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_10 : starHelperPair 3 10 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_11 : starHelperPair 3 11 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_12 : starHelperPair 3 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_13 : starHelperPair 3 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_14 : starHelperPair 3 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_15 : starHelperPair 3 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_17 : starHelperPair 3 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_18 : starHelperPair 3 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_19 : starHelperPair 3 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_20 : starHelperPair 3 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_21 : starHelperPair 3 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_23 : starHelperPair 3 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_24 : starHelperPair 3 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_26 : starHelperPair 3 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_27 : starHelperPair 3 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_28 : starHelperPair 3 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_29 : starHelperPair 3 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_30 : starHelperPair 3 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_31 : starHelperPair 3 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_33 : starHelperPair 3 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_34 : starHelperPair 3 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_35 : starHelperPair 3 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_36 : starHelperPair 3 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_38 : starHelperPair 3 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_39 : starHelperPair 3 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_40 : starHelperPair 3 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_41 : starHelperPair 3 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_43 : starHelperPair 3 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_44 : starHelperPair 3 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_45 : starHelperPair 3 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_46 : starHelperPair 3 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_47 : starHelperPair 3 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_48 : starHelperPair 3 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_49 : starHelperPair 3 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_50 : starHelperPair 3 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_51 : starHelperPair 3 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_52 : starHelperPair 3 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_53 : starHelperPair 3 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_54 : starHelperPair 3 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_55 : starHelperPair 3 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_56 : starHelperPair 3 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_57 : starHelperPair 3 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_58 : starHelperPair 3 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_59 : starHelperPair 3 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_60 : starHelperPair 3 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_61 : starHelperPair 3 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_62 : starHelperPair 3 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_3_63 : starHelperPair 3 63 = false := by
  decide +kernel

lemma starHelperRow_3 : starHelperRow 3 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_3_5, starHelperPair_3_6, starHelperPair_3_7, starHelperPair_3_9, starHelperPair_3_10, starHelperPair_3_11, starHelperPair_3_12, starHelperPair_3_13, starHelperPair_3_14, starHelperPair_3_15, starHelperPair_3_17, starHelperPair_3_18, starHelperPair_3_19, starHelperPair_3_20, starHelperPair_3_21, starHelperPair_3_23, starHelperPair_3_24, starHelperPair_3_26, starHelperPair_3_27, starHelperPair_3_28, starHelperPair_3_29, starHelperPair_3_30, starHelperPair_3_31, starHelperPair_3_33, starHelperPair_3_34, starHelperPair_3_35, starHelperPair_3_36, starHelperPair_3_38, starHelperPair_3_39, starHelperPair_3_40, starHelperPair_3_41, starHelperPair_3_43, starHelperPair_3_44, starHelperPair_3_45, starHelperPair_3_46, starHelperPair_3_47, starHelperPair_3_48, starHelperPair_3_49, starHelperPair_3_50, starHelperPair_3_51, starHelperPair_3_52, starHelperPair_3_53, starHelperPair_3_54, starHelperPair_3_55, starHelperPair_3_56, starHelperPair_3_57, starHelperPair_3_58, starHelperPair_3_59, starHelperPair_3_60, starHelperPair_3_61, starHelperPair_3_62, starHelperPair_3_63]

end PEqualNP.Outside.L_meta_2592
