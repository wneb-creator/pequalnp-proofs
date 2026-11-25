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
lemma starHelperPair_5_6 : starHelperPair 5 6 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_7 : starHelperPair 5 7 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_9 : starHelperPair 5 9 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_10 : starHelperPair 5 10 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_11 : starHelperPair 5 11 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_12 : starHelperPair 5 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_13 : starHelperPair 5 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_14 : starHelperPair 5 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_15 : starHelperPair 5 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_17 : starHelperPair 5 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_18 : starHelperPair 5 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_19 : starHelperPair 5 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_20 : starHelperPair 5 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_21 : starHelperPair 5 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_23 : starHelperPair 5 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_24 : starHelperPair 5 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_26 : starHelperPair 5 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_27 : starHelperPair 5 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_28 : starHelperPair 5 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_29 : starHelperPair 5 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_30 : starHelperPair 5 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_31 : starHelperPair 5 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_33 : starHelperPair 5 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_34 : starHelperPair 5 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_35 : starHelperPair 5 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_36 : starHelperPair 5 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_38 : starHelperPair 5 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_39 : starHelperPair 5 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_40 : starHelperPair 5 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_41 : starHelperPair 5 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_43 : starHelperPair 5 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_44 : starHelperPair 5 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_45 : starHelperPair 5 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_46 : starHelperPair 5 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_47 : starHelperPair 5 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_48 : starHelperPair 5 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_49 : starHelperPair 5 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_50 : starHelperPair 5 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_51 : starHelperPair 5 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_52 : starHelperPair 5 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_53 : starHelperPair 5 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_54 : starHelperPair 5 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_55 : starHelperPair 5 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_56 : starHelperPair 5 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_57 : starHelperPair 5 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_58 : starHelperPair 5 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_59 : starHelperPair 5 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_60 : starHelperPair 5 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_61 : starHelperPair 5 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_62 : starHelperPair 5 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_5_63 : starHelperPair 5 63 = false := by
  decide +kernel

lemma starHelperRow_5 : starHelperRow 5 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_5_6, starHelperPair_5_7, starHelperPair_5_9, starHelperPair_5_10, starHelperPair_5_11, starHelperPair_5_12, starHelperPair_5_13, starHelperPair_5_14, starHelperPair_5_15, starHelperPair_5_17, starHelperPair_5_18, starHelperPair_5_19, starHelperPair_5_20, starHelperPair_5_21, starHelperPair_5_23, starHelperPair_5_24, starHelperPair_5_26, starHelperPair_5_27, starHelperPair_5_28, starHelperPair_5_29, starHelperPair_5_30, starHelperPair_5_31, starHelperPair_5_33, starHelperPair_5_34, starHelperPair_5_35, starHelperPair_5_36, starHelperPair_5_38, starHelperPair_5_39, starHelperPair_5_40, starHelperPair_5_41, starHelperPair_5_43, starHelperPair_5_44, starHelperPair_5_45, starHelperPair_5_46, starHelperPair_5_47, starHelperPair_5_48, starHelperPair_5_49, starHelperPair_5_50, starHelperPair_5_51, starHelperPair_5_52, starHelperPair_5_53, starHelperPair_5_54, starHelperPair_5_55, starHelperPair_5_56, starHelperPair_5_57, starHelperPair_5_58, starHelperPair_5_59, starHelperPair_5_60, starHelperPair_5_61, starHelperPair_5_62, starHelperPair_5_63]

end PEqualNP.Outside.L_meta_2592
