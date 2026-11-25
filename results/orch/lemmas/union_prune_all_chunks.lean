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

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_7 : starHelperPair 6 7 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_9 : starHelperPair 6 9 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_10 : starHelperPair 6 10 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_11 : starHelperPair 6 11 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_12 : starHelperPair 6 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_13 : starHelperPair 6 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_14 : starHelperPair 6 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_15 : starHelperPair 6 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_17 : starHelperPair 6 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_18 : starHelperPair 6 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_19 : starHelperPair 6 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_20 : starHelperPair 6 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_21 : starHelperPair 6 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_23 : starHelperPair 6 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_24 : starHelperPair 6 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_26 : starHelperPair 6 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_27 : starHelperPair 6 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_28 : starHelperPair 6 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_29 : starHelperPair 6 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_30 : starHelperPair 6 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_31 : starHelperPair 6 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_33 : starHelperPair 6 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_34 : starHelperPair 6 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_35 : starHelperPair 6 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_36 : starHelperPair 6 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_38 : starHelperPair 6 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_39 : starHelperPair 6 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_40 : starHelperPair 6 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_41 : starHelperPair 6 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_43 : starHelperPair 6 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_44 : starHelperPair 6 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_45 : starHelperPair 6 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_46 : starHelperPair 6 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_47 : starHelperPair 6 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_48 : starHelperPair 6 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_49 : starHelperPair 6 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_50 : starHelperPair 6 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_51 : starHelperPair 6 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_52 : starHelperPair 6 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_53 : starHelperPair 6 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_54 : starHelperPair 6 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_55 : starHelperPair 6 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_56 : starHelperPair 6 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_57 : starHelperPair 6 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_58 : starHelperPair 6 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_59 : starHelperPair 6 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_60 : starHelperPair 6 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_61 : starHelperPair 6 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_62 : starHelperPair 6 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_6_63 : starHelperPair 6 63 = false := by
  decide +kernel

lemma starHelperRow_6 : starHelperRow 6 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_6_7, starHelperPair_6_9, starHelperPair_6_10, starHelperPair_6_11, starHelperPair_6_12, starHelperPair_6_13, starHelperPair_6_14, starHelperPair_6_15, starHelperPair_6_17, starHelperPair_6_18, starHelperPair_6_19, starHelperPair_6_20, starHelperPair_6_21, starHelperPair_6_23, starHelperPair_6_24, starHelperPair_6_26, starHelperPair_6_27, starHelperPair_6_28, starHelperPair_6_29, starHelperPair_6_30, starHelperPair_6_31, starHelperPair_6_33, starHelperPair_6_34, starHelperPair_6_35, starHelperPair_6_36, starHelperPair_6_38, starHelperPair_6_39, starHelperPair_6_40, starHelperPair_6_41, starHelperPair_6_43, starHelperPair_6_44, starHelperPair_6_45, starHelperPair_6_46, starHelperPair_6_47, starHelperPair_6_48, starHelperPair_6_49, starHelperPair_6_50, starHelperPair_6_51, starHelperPair_6_52, starHelperPair_6_53, starHelperPair_6_54, starHelperPair_6_55, starHelperPair_6_56, starHelperPair_6_57, starHelperPair_6_58, starHelperPair_6_59, starHelperPair_6_60, starHelperPair_6_61, starHelperPair_6_62, starHelperPair_6_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_9 : starHelperPair 7 9 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_10 : starHelperPair 7 10 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_11 : starHelperPair 7 11 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_12 : starHelperPair 7 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_13 : starHelperPair 7 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_14 : starHelperPair 7 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_15 : starHelperPair 7 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_17 : starHelperPair 7 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_18 : starHelperPair 7 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_19 : starHelperPair 7 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_20 : starHelperPair 7 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_21 : starHelperPair 7 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_23 : starHelperPair 7 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_24 : starHelperPair 7 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_26 : starHelperPair 7 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_27 : starHelperPair 7 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_28 : starHelperPair 7 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_29 : starHelperPair 7 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_30 : starHelperPair 7 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_31 : starHelperPair 7 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_33 : starHelperPair 7 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_34 : starHelperPair 7 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_35 : starHelperPair 7 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_36 : starHelperPair 7 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_38 : starHelperPair 7 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_39 : starHelperPair 7 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_40 : starHelperPair 7 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_41 : starHelperPair 7 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_43 : starHelperPair 7 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_44 : starHelperPair 7 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_45 : starHelperPair 7 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_46 : starHelperPair 7 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_47 : starHelperPair 7 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_48 : starHelperPair 7 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_49 : starHelperPair 7 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_50 : starHelperPair 7 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_51 : starHelperPair 7 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_52 : starHelperPair 7 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_53 : starHelperPair 7 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_54 : starHelperPair 7 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_55 : starHelperPair 7 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_56 : starHelperPair 7 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_57 : starHelperPair 7 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_58 : starHelperPair 7 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_59 : starHelperPair 7 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_60 : starHelperPair 7 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_61 : starHelperPair 7 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_62 : starHelperPair 7 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_7_63 : starHelperPair 7 63 = false := by
  decide +kernel

lemma starHelperRow_7 : starHelperRow 7 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_7_9, starHelperPair_7_10, starHelperPair_7_11, starHelperPair_7_12, starHelperPair_7_13, starHelperPair_7_14, starHelperPair_7_15, starHelperPair_7_17, starHelperPair_7_18, starHelperPair_7_19, starHelperPair_7_20, starHelperPair_7_21, starHelperPair_7_23, starHelperPair_7_24, starHelperPair_7_26, starHelperPair_7_27, starHelperPair_7_28, starHelperPair_7_29, starHelperPair_7_30, starHelperPair_7_31, starHelperPair_7_33, starHelperPair_7_34, starHelperPair_7_35, starHelperPair_7_36, starHelperPair_7_38, starHelperPair_7_39, starHelperPair_7_40, starHelperPair_7_41, starHelperPair_7_43, starHelperPair_7_44, starHelperPair_7_45, starHelperPair_7_46, starHelperPair_7_47, starHelperPair_7_48, starHelperPair_7_49, starHelperPair_7_50, starHelperPair_7_51, starHelperPair_7_52, starHelperPair_7_53, starHelperPair_7_54, starHelperPair_7_55, starHelperPair_7_56, starHelperPair_7_57, starHelperPair_7_58, starHelperPair_7_59, starHelperPair_7_60, starHelperPair_7_61, starHelperPair_7_62, starHelperPair_7_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_10 : starHelperPair 9 10 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_11 : starHelperPair 9 11 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_12 : starHelperPair 9 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_13 : starHelperPair 9 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_14 : starHelperPair 9 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_15 : starHelperPair 9 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_17 : starHelperPair 9 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_18 : starHelperPair 9 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_19 : starHelperPair 9 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_20 : starHelperPair 9 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_21 : starHelperPair 9 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_23 : starHelperPair 9 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_24 : starHelperPair 9 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_26 : starHelperPair 9 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_27 : starHelperPair 9 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_28 : starHelperPair 9 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_29 : starHelperPair 9 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_30 : starHelperPair 9 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_31 : starHelperPair 9 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_33 : starHelperPair 9 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_34 : starHelperPair 9 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_35 : starHelperPair 9 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_36 : starHelperPair 9 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_38 : starHelperPair 9 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_39 : starHelperPair 9 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_40 : starHelperPair 9 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_41 : starHelperPair 9 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_43 : starHelperPair 9 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_44 : starHelperPair 9 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_45 : starHelperPair 9 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_46 : starHelperPair 9 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_47 : starHelperPair 9 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_48 : starHelperPair 9 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_49 : starHelperPair 9 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_50 : starHelperPair 9 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_51 : starHelperPair 9 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_52 : starHelperPair 9 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_53 : starHelperPair 9 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_54 : starHelperPair 9 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_55 : starHelperPair 9 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_56 : starHelperPair 9 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_57 : starHelperPair 9 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_58 : starHelperPair 9 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_59 : starHelperPair 9 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_60 : starHelperPair 9 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_61 : starHelperPair 9 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_62 : starHelperPair 9 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_9_63 : starHelperPair 9 63 = false := by
  decide +kernel

lemma starHelperRow_9 : starHelperRow 9 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_9_10, starHelperPair_9_11, starHelperPair_9_12, starHelperPair_9_13, starHelperPair_9_14, starHelperPair_9_15, starHelperPair_9_17, starHelperPair_9_18, starHelperPair_9_19, starHelperPair_9_20, starHelperPair_9_21, starHelperPair_9_23, starHelperPair_9_24, starHelperPair_9_26, starHelperPair_9_27, starHelperPair_9_28, starHelperPair_9_29, starHelperPair_9_30, starHelperPair_9_31, starHelperPair_9_33, starHelperPair_9_34, starHelperPair_9_35, starHelperPair_9_36, starHelperPair_9_38, starHelperPair_9_39, starHelperPair_9_40, starHelperPair_9_41, starHelperPair_9_43, starHelperPair_9_44, starHelperPair_9_45, starHelperPair_9_46, starHelperPair_9_47, starHelperPair_9_48, starHelperPair_9_49, starHelperPair_9_50, starHelperPair_9_51, starHelperPair_9_52, starHelperPair_9_53, starHelperPair_9_54, starHelperPair_9_55, starHelperPair_9_56, starHelperPair_9_57, starHelperPair_9_58, starHelperPair_9_59, starHelperPair_9_60, starHelperPair_9_61, starHelperPair_9_62, starHelperPair_9_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_11 : starHelperPair 10 11 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_12 : starHelperPair 10 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_13 : starHelperPair 10 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_14 : starHelperPair 10 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_15 : starHelperPair 10 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_17 : starHelperPair 10 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_18 : starHelperPair 10 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_19 : starHelperPair 10 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_20 : starHelperPair 10 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_21 : starHelperPair 10 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_23 : starHelperPair 10 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_24 : starHelperPair 10 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_26 : starHelperPair 10 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_27 : starHelperPair 10 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_28 : starHelperPair 10 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_29 : starHelperPair 10 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_30 : starHelperPair 10 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_31 : starHelperPair 10 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_33 : starHelperPair 10 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_34 : starHelperPair 10 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_35 : starHelperPair 10 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_36 : starHelperPair 10 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_38 : starHelperPair 10 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_39 : starHelperPair 10 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_40 : starHelperPair 10 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_41 : starHelperPair 10 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_43 : starHelperPair 10 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_44 : starHelperPair 10 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_45 : starHelperPair 10 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_46 : starHelperPair 10 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_47 : starHelperPair 10 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_48 : starHelperPair 10 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_49 : starHelperPair 10 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_50 : starHelperPair 10 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_51 : starHelperPair 10 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_52 : starHelperPair 10 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_53 : starHelperPair 10 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_54 : starHelperPair 10 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_55 : starHelperPair 10 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_56 : starHelperPair 10 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_57 : starHelperPair 10 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_58 : starHelperPair 10 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_59 : starHelperPair 10 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_60 : starHelperPair 10 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_61 : starHelperPair 10 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_62 : starHelperPair 10 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_10_63 : starHelperPair 10 63 = false := by
  decide +kernel

lemma starHelperRow_10 : starHelperRow 10 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_10_11, starHelperPair_10_12, starHelperPair_10_13, starHelperPair_10_14, starHelperPair_10_15, starHelperPair_10_17, starHelperPair_10_18, starHelperPair_10_19, starHelperPair_10_20, starHelperPair_10_21, starHelperPair_10_23, starHelperPair_10_24, starHelperPair_10_26, starHelperPair_10_27, starHelperPair_10_28, starHelperPair_10_29, starHelperPair_10_30, starHelperPair_10_31, starHelperPair_10_33, starHelperPair_10_34, starHelperPair_10_35, starHelperPair_10_36, starHelperPair_10_38, starHelperPair_10_39, starHelperPair_10_40, starHelperPair_10_41, starHelperPair_10_43, starHelperPair_10_44, starHelperPair_10_45, starHelperPair_10_46, starHelperPair_10_47, starHelperPair_10_48, starHelperPair_10_49, starHelperPair_10_50, starHelperPair_10_51, starHelperPair_10_52, starHelperPair_10_53, starHelperPair_10_54, starHelperPair_10_55, starHelperPair_10_56, starHelperPair_10_57, starHelperPair_10_58, starHelperPair_10_59, starHelperPair_10_60, starHelperPair_10_61, starHelperPair_10_62, starHelperPair_10_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_12 : starHelperPair 11 12 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_13 : starHelperPair 11 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_14 : starHelperPair 11 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_15 : starHelperPair 11 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_17 : starHelperPair 11 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_18 : starHelperPair 11 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_19 : starHelperPair 11 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_20 : starHelperPair 11 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_21 : starHelperPair 11 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_23 : starHelperPair 11 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_24 : starHelperPair 11 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_26 : starHelperPair 11 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_27 : starHelperPair 11 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_28 : starHelperPair 11 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_29 : starHelperPair 11 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_30 : starHelperPair 11 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_31 : starHelperPair 11 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_33 : starHelperPair 11 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_34 : starHelperPair 11 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_35 : starHelperPair 11 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_36 : starHelperPair 11 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_38 : starHelperPair 11 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_39 : starHelperPair 11 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_40 : starHelperPair 11 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_41 : starHelperPair 11 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_43 : starHelperPair 11 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_44 : starHelperPair 11 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_45 : starHelperPair 11 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_46 : starHelperPair 11 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_47 : starHelperPair 11 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_48 : starHelperPair 11 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_49 : starHelperPair 11 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_50 : starHelperPair 11 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_51 : starHelperPair 11 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_52 : starHelperPair 11 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_53 : starHelperPair 11 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_54 : starHelperPair 11 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_55 : starHelperPair 11 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_56 : starHelperPair 11 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_57 : starHelperPair 11 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_58 : starHelperPair 11 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_59 : starHelperPair 11 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_60 : starHelperPair 11 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_61 : starHelperPair 11 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_62 : starHelperPair 11 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_11_63 : starHelperPair 11 63 = false := by
  decide +kernel

lemma starHelperRow_11 : starHelperRow 11 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_11_12, starHelperPair_11_13, starHelperPair_11_14, starHelperPair_11_15, starHelperPair_11_17, starHelperPair_11_18, starHelperPair_11_19, starHelperPair_11_20, starHelperPair_11_21, starHelperPair_11_23, starHelperPair_11_24, starHelperPair_11_26, starHelperPair_11_27, starHelperPair_11_28, starHelperPair_11_29, starHelperPair_11_30, starHelperPair_11_31, starHelperPair_11_33, starHelperPair_11_34, starHelperPair_11_35, starHelperPair_11_36, starHelperPair_11_38, starHelperPair_11_39, starHelperPair_11_40, starHelperPair_11_41, starHelperPair_11_43, starHelperPair_11_44, starHelperPair_11_45, starHelperPair_11_46, starHelperPair_11_47, starHelperPair_11_48, starHelperPair_11_49, starHelperPair_11_50, starHelperPair_11_51, starHelperPair_11_52, starHelperPair_11_53, starHelperPair_11_54, starHelperPair_11_55, starHelperPair_11_56, starHelperPair_11_57, starHelperPair_11_58, starHelperPair_11_59, starHelperPair_11_60, starHelperPair_11_61, starHelperPair_11_62, starHelperPair_11_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_13 : starHelperPair 12 13 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_14 : starHelperPair 12 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_15 : starHelperPair 12 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_17 : starHelperPair 12 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_18 : starHelperPair 12 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_19 : starHelperPair 12 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_20 : starHelperPair 12 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_21 : starHelperPair 12 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_23 : starHelperPair 12 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_24 : starHelperPair 12 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_26 : starHelperPair 12 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_27 : starHelperPair 12 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_28 : starHelperPair 12 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_29 : starHelperPair 12 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_30 : starHelperPair 12 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_31 : starHelperPair 12 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_33 : starHelperPair 12 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_34 : starHelperPair 12 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_35 : starHelperPair 12 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_36 : starHelperPair 12 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_38 : starHelperPair 12 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_39 : starHelperPair 12 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_40 : starHelperPair 12 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_41 : starHelperPair 12 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_43 : starHelperPair 12 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_44 : starHelperPair 12 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_45 : starHelperPair 12 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_46 : starHelperPair 12 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_47 : starHelperPair 12 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_48 : starHelperPair 12 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_49 : starHelperPair 12 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_50 : starHelperPair 12 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_51 : starHelperPair 12 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_52 : starHelperPair 12 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_53 : starHelperPair 12 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_54 : starHelperPair 12 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_55 : starHelperPair 12 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_56 : starHelperPair 12 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_57 : starHelperPair 12 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_58 : starHelperPair 12 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_59 : starHelperPair 12 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_60 : starHelperPair 12 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_61 : starHelperPair 12 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_62 : starHelperPair 12 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_12_63 : starHelperPair 12 63 = false := by
  decide +kernel

lemma starHelperRow_12 : starHelperRow 12 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_12_13, starHelperPair_12_14, starHelperPair_12_15, starHelperPair_12_17, starHelperPair_12_18, starHelperPair_12_19, starHelperPair_12_20, starHelperPair_12_21, starHelperPair_12_23, starHelperPair_12_24, starHelperPair_12_26, starHelperPair_12_27, starHelperPair_12_28, starHelperPair_12_29, starHelperPair_12_30, starHelperPair_12_31, starHelperPair_12_33, starHelperPair_12_34, starHelperPair_12_35, starHelperPair_12_36, starHelperPair_12_38, starHelperPair_12_39, starHelperPair_12_40, starHelperPair_12_41, starHelperPair_12_43, starHelperPair_12_44, starHelperPair_12_45, starHelperPair_12_46, starHelperPair_12_47, starHelperPair_12_48, starHelperPair_12_49, starHelperPair_12_50, starHelperPair_12_51, starHelperPair_12_52, starHelperPair_12_53, starHelperPair_12_54, starHelperPair_12_55, starHelperPair_12_56, starHelperPair_12_57, starHelperPair_12_58, starHelperPair_12_59, starHelperPair_12_60, starHelperPair_12_61, starHelperPair_12_62, starHelperPair_12_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_14 : starHelperPair 13 14 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_15 : starHelperPair 13 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_17 : starHelperPair 13 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_18 : starHelperPair 13 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_19 : starHelperPair 13 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_20 : starHelperPair 13 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_21 : starHelperPair 13 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_23 : starHelperPair 13 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_24 : starHelperPair 13 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_26 : starHelperPair 13 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_27 : starHelperPair 13 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_28 : starHelperPair 13 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_29 : starHelperPair 13 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_30 : starHelperPair 13 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_31 : starHelperPair 13 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_33 : starHelperPair 13 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_34 : starHelperPair 13 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_35 : starHelperPair 13 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_36 : starHelperPair 13 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_38 : starHelperPair 13 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_39 : starHelperPair 13 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_40 : starHelperPair 13 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_41 : starHelperPair 13 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_43 : starHelperPair 13 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_44 : starHelperPair 13 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_45 : starHelperPair 13 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_46 : starHelperPair 13 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_47 : starHelperPair 13 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_48 : starHelperPair 13 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_49 : starHelperPair 13 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_50 : starHelperPair 13 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_51 : starHelperPair 13 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_52 : starHelperPair 13 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_53 : starHelperPair 13 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_54 : starHelperPair 13 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_55 : starHelperPair 13 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_56 : starHelperPair 13 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_57 : starHelperPair 13 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_58 : starHelperPair 13 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_59 : starHelperPair 13 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_60 : starHelperPair 13 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_61 : starHelperPair 13 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_62 : starHelperPair 13 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_13_63 : starHelperPair 13 63 = false := by
  decide +kernel

lemma starHelperRow_13 : starHelperRow 13 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_13_14, starHelperPair_13_15, starHelperPair_13_17, starHelperPair_13_18, starHelperPair_13_19, starHelperPair_13_20, starHelperPair_13_21, starHelperPair_13_23, starHelperPair_13_24, starHelperPair_13_26, starHelperPair_13_27, starHelperPair_13_28, starHelperPair_13_29, starHelperPair_13_30, starHelperPair_13_31, starHelperPair_13_33, starHelperPair_13_34, starHelperPair_13_35, starHelperPair_13_36, starHelperPair_13_38, starHelperPair_13_39, starHelperPair_13_40, starHelperPair_13_41, starHelperPair_13_43, starHelperPair_13_44, starHelperPair_13_45, starHelperPair_13_46, starHelperPair_13_47, starHelperPair_13_48, starHelperPair_13_49, starHelperPair_13_50, starHelperPair_13_51, starHelperPair_13_52, starHelperPair_13_53, starHelperPair_13_54, starHelperPair_13_55, starHelperPair_13_56, starHelperPair_13_57, starHelperPair_13_58, starHelperPair_13_59, starHelperPair_13_60, starHelperPair_13_61, starHelperPair_13_62, starHelperPair_13_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_15 : starHelperPair 14 15 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_17 : starHelperPair 14 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_18 : starHelperPair 14 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_19 : starHelperPair 14 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_20 : starHelperPair 14 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_21 : starHelperPair 14 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_23 : starHelperPair 14 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_24 : starHelperPair 14 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_26 : starHelperPair 14 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_27 : starHelperPair 14 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_28 : starHelperPair 14 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_29 : starHelperPair 14 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_30 : starHelperPair 14 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_31 : starHelperPair 14 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_33 : starHelperPair 14 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_34 : starHelperPair 14 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_35 : starHelperPair 14 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_36 : starHelperPair 14 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_38 : starHelperPair 14 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_39 : starHelperPair 14 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_40 : starHelperPair 14 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_41 : starHelperPair 14 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_43 : starHelperPair 14 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_44 : starHelperPair 14 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_45 : starHelperPair 14 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_46 : starHelperPair 14 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_47 : starHelperPair 14 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_48 : starHelperPair 14 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_49 : starHelperPair 14 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_50 : starHelperPair 14 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_51 : starHelperPair 14 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_52 : starHelperPair 14 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_53 : starHelperPair 14 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_54 : starHelperPair 14 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_55 : starHelperPair 14 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_56 : starHelperPair 14 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_57 : starHelperPair 14 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_58 : starHelperPair 14 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_59 : starHelperPair 14 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_60 : starHelperPair 14 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_61 : starHelperPair 14 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_62 : starHelperPair 14 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_14_63 : starHelperPair 14 63 = false := by
  decide +kernel

lemma starHelperRow_14 : starHelperRow 14 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_14_15, starHelperPair_14_17, starHelperPair_14_18, starHelperPair_14_19, starHelperPair_14_20, starHelperPair_14_21, starHelperPair_14_23, starHelperPair_14_24, starHelperPair_14_26, starHelperPair_14_27, starHelperPair_14_28, starHelperPair_14_29, starHelperPair_14_30, starHelperPair_14_31, starHelperPair_14_33, starHelperPair_14_34, starHelperPair_14_35, starHelperPair_14_36, starHelperPair_14_38, starHelperPair_14_39, starHelperPair_14_40, starHelperPair_14_41, starHelperPair_14_43, starHelperPair_14_44, starHelperPair_14_45, starHelperPair_14_46, starHelperPair_14_47, starHelperPair_14_48, starHelperPair_14_49, starHelperPair_14_50, starHelperPair_14_51, starHelperPair_14_52, starHelperPair_14_53, starHelperPair_14_54, starHelperPair_14_55, starHelperPair_14_56, starHelperPair_14_57, starHelperPair_14_58, starHelperPair_14_59, starHelperPair_14_60, starHelperPair_14_61, starHelperPair_14_62, starHelperPair_14_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_17 : starHelperPair 15 17 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_18 : starHelperPair 15 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_19 : starHelperPair 15 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_20 : starHelperPair 15 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_21 : starHelperPair 15 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_23 : starHelperPair 15 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_24 : starHelperPair 15 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_26 : starHelperPair 15 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_27 : starHelperPair 15 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_28 : starHelperPair 15 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_29 : starHelperPair 15 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_30 : starHelperPair 15 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_31 : starHelperPair 15 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_33 : starHelperPair 15 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_34 : starHelperPair 15 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_35 : starHelperPair 15 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_36 : starHelperPair 15 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_38 : starHelperPair 15 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_39 : starHelperPair 15 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_40 : starHelperPair 15 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_41 : starHelperPair 15 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_43 : starHelperPair 15 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_44 : starHelperPair 15 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_45 : starHelperPair 15 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_46 : starHelperPair 15 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_47 : starHelperPair 15 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_48 : starHelperPair 15 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_49 : starHelperPair 15 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_50 : starHelperPair 15 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_51 : starHelperPair 15 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_52 : starHelperPair 15 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_53 : starHelperPair 15 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_54 : starHelperPair 15 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_55 : starHelperPair 15 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_56 : starHelperPair 15 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_57 : starHelperPair 15 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_58 : starHelperPair 15 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_59 : starHelperPair 15 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_60 : starHelperPair 15 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_61 : starHelperPair 15 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_62 : starHelperPair 15 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_15_63 : starHelperPair 15 63 = false := by
  decide +kernel

lemma starHelperRow_15 : starHelperRow 15 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_15_17, starHelperPair_15_18, starHelperPair_15_19, starHelperPair_15_20, starHelperPair_15_21, starHelperPair_15_23, starHelperPair_15_24, starHelperPair_15_26, starHelperPair_15_27, starHelperPair_15_28, starHelperPair_15_29, starHelperPair_15_30, starHelperPair_15_31, starHelperPair_15_33, starHelperPair_15_34, starHelperPair_15_35, starHelperPair_15_36, starHelperPair_15_38, starHelperPair_15_39, starHelperPair_15_40, starHelperPair_15_41, starHelperPair_15_43, starHelperPair_15_44, starHelperPair_15_45, starHelperPair_15_46, starHelperPair_15_47, starHelperPair_15_48, starHelperPair_15_49, starHelperPair_15_50, starHelperPair_15_51, starHelperPair_15_52, starHelperPair_15_53, starHelperPair_15_54, starHelperPair_15_55, starHelperPair_15_56, starHelperPair_15_57, starHelperPair_15_58, starHelperPair_15_59, starHelperPair_15_60, starHelperPair_15_61, starHelperPair_15_62, starHelperPair_15_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_18 : starHelperPair 17 18 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_19 : starHelperPair 17 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_20 : starHelperPair 17 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_21 : starHelperPair 17 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_23 : starHelperPair 17 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_24 : starHelperPair 17 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_26 : starHelperPair 17 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_27 : starHelperPair 17 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_28 : starHelperPair 17 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_29 : starHelperPair 17 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_30 : starHelperPair 17 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_31 : starHelperPair 17 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_33 : starHelperPair 17 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_34 : starHelperPair 17 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_35 : starHelperPair 17 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_36 : starHelperPair 17 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_38 : starHelperPair 17 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_39 : starHelperPair 17 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_40 : starHelperPair 17 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_41 : starHelperPair 17 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_43 : starHelperPair 17 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_44 : starHelperPair 17 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_45 : starHelperPair 17 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_46 : starHelperPair 17 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_47 : starHelperPair 17 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_48 : starHelperPair 17 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_49 : starHelperPair 17 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_50 : starHelperPair 17 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_51 : starHelperPair 17 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_52 : starHelperPair 17 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_53 : starHelperPair 17 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_54 : starHelperPair 17 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_55 : starHelperPair 17 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_56 : starHelperPair 17 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_57 : starHelperPair 17 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_58 : starHelperPair 17 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_59 : starHelperPair 17 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_60 : starHelperPair 17 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_61 : starHelperPair 17 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_62 : starHelperPair 17 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_17_63 : starHelperPair 17 63 = false := by
  decide +kernel

lemma starHelperRow_17 : starHelperRow 17 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_17_18, starHelperPair_17_19, starHelperPair_17_20, starHelperPair_17_21, starHelperPair_17_23, starHelperPair_17_24, starHelperPair_17_26, starHelperPair_17_27, starHelperPair_17_28, starHelperPair_17_29, starHelperPair_17_30, starHelperPair_17_31, starHelperPair_17_33, starHelperPair_17_34, starHelperPair_17_35, starHelperPair_17_36, starHelperPair_17_38, starHelperPair_17_39, starHelperPair_17_40, starHelperPair_17_41, starHelperPair_17_43, starHelperPair_17_44, starHelperPair_17_45, starHelperPair_17_46, starHelperPair_17_47, starHelperPair_17_48, starHelperPair_17_49, starHelperPair_17_50, starHelperPair_17_51, starHelperPair_17_52, starHelperPair_17_53, starHelperPair_17_54, starHelperPair_17_55, starHelperPair_17_56, starHelperPair_17_57, starHelperPair_17_58, starHelperPair_17_59, starHelperPair_17_60, starHelperPair_17_61, starHelperPair_17_62, starHelperPair_17_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_19 : starHelperPair 18 19 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_20 : starHelperPair 18 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_21 : starHelperPair 18 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_23 : starHelperPair 18 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_24 : starHelperPair 18 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_26 : starHelperPair 18 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_27 : starHelperPair 18 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_28 : starHelperPair 18 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_29 : starHelperPair 18 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_30 : starHelperPair 18 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_31 : starHelperPair 18 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_33 : starHelperPair 18 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_34 : starHelperPair 18 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_35 : starHelperPair 18 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_36 : starHelperPair 18 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_38 : starHelperPair 18 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_39 : starHelperPair 18 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_40 : starHelperPair 18 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_41 : starHelperPair 18 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_43 : starHelperPair 18 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_44 : starHelperPair 18 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_45 : starHelperPair 18 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_46 : starHelperPair 18 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_47 : starHelperPair 18 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_48 : starHelperPair 18 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_49 : starHelperPair 18 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_50 : starHelperPair 18 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_51 : starHelperPair 18 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_52 : starHelperPair 18 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_53 : starHelperPair 18 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_54 : starHelperPair 18 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_55 : starHelperPair 18 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_56 : starHelperPair 18 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_57 : starHelperPair 18 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_58 : starHelperPair 18 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_59 : starHelperPair 18 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_60 : starHelperPair 18 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_61 : starHelperPair 18 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_62 : starHelperPair 18 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_18_63 : starHelperPair 18 63 = false := by
  decide +kernel

lemma starHelperRow_18 : starHelperRow 18 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_18_19, starHelperPair_18_20, starHelperPair_18_21, starHelperPair_18_23, starHelperPair_18_24, starHelperPair_18_26, starHelperPair_18_27, starHelperPair_18_28, starHelperPair_18_29, starHelperPair_18_30, starHelperPair_18_31, starHelperPair_18_33, starHelperPair_18_34, starHelperPair_18_35, starHelperPair_18_36, starHelperPair_18_38, starHelperPair_18_39, starHelperPair_18_40, starHelperPair_18_41, starHelperPair_18_43, starHelperPair_18_44, starHelperPair_18_45, starHelperPair_18_46, starHelperPair_18_47, starHelperPair_18_48, starHelperPair_18_49, starHelperPair_18_50, starHelperPair_18_51, starHelperPair_18_52, starHelperPair_18_53, starHelperPair_18_54, starHelperPair_18_55, starHelperPair_18_56, starHelperPair_18_57, starHelperPair_18_58, starHelperPair_18_59, starHelperPair_18_60, starHelperPair_18_61, starHelperPair_18_62, starHelperPair_18_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_20 : starHelperPair 19 20 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_21 : starHelperPair 19 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_23 : starHelperPair 19 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_24 : starHelperPair 19 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_26 : starHelperPair 19 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_27 : starHelperPair 19 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_28 : starHelperPair 19 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_29 : starHelperPair 19 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_30 : starHelperPair 19 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_31 : starHelperPair 19 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_33 : starHelperPair 19 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_34 : starHelperPair 19 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_35 : starHelperPair 19 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_36 : starHelperPair 19 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_38 : starHelperPair 19 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_39 : starHelperPair 19 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_40 : starHelperPair 19 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_41 : starHelperPair 19 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_43 : starHelperPair 19 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_44 : starHelperPair 19 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_45 : starHelperPair 19 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_46 : starHelperPair 19 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_47 : starHelperPair 19 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_48 : starHelperPair 19 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_49 : starHelperPair 19 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_50 : starHelperPair 19 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_51 : starHelperPair 19 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_52 : starHelperPair 19 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_53 : starHelperPair 19 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_54 : starHelperPair 19 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_55 : starHelperPair 19 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_56 : starHelperPair 19 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_57 : starHelperPair 19 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_58 : starHelperPair 19 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_59 : starHelperPair 19 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_60 : starHelperPair 19 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_61 : starHelperPair 19 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_62 : starHelperPair 19 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_19_63 : starHelperPair 19 63 = false := by
  decide +kernel

lemma starHelperRow_19 : starHelperRow 19 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_19_20, starHelperPair_19_21, starHelperPair_19_23, starHelperPair_19_24, starHelperPair_19_26, starHelperPair_19_27, starHelperPair_19_28, starHelperPair_19_29, starHelperPair_19_30, starHelperPair_19_31, starHelperPair_19_33, starHelperPair_19_34, starHelperPair_19_35, starHelperPair_19_36, starHelperPair_19_38, starHelperPair_19_39, starHelperPair_19_40, starHelperPair_19_41, starHelperPair_19_43, starHelperPair_19_44, starHelperPair_19_45, starHelperPair_19_46, starHelperPair_19_47, starHelperPair_19_48, starHelperPair_19_49, starHelperPair_19_50, starHelperPair_19_51, starHelperPair_19_52, starHelperPair_19_53, starHelperPair_19_54, starHelperPair_19_55, starHelperPair_19_56, starHelperPair_19_57, starHelperPair_19_58, starHelperPair_19_59, starHelperPair_19_60, starHelperPair_19_61, starHelperPair_19_62, starHelperPair_19_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_21 : starHelperPair 20 21 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_23 : starHelperPair 20 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_24 : starHelperPair 20 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_26 : starHelperPair 20 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_27 : starHelperPair 20 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_28 : starHelperPair 20 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_29 : starHelperPair 20 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_30 : starHelperPair 20 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_31 : starHelperPair 20 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_33 : starHelperPair 20 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_34 : starHelperPair 20 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_35 : starHelperPair 20 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_36 : starHelperPair 20 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_38 : starHelperPair 20 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_39 : starHelperPair 20 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_40 : starHelperPair 20 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_41 : starHelperPair 20 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_43 : starHelperPair 20 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_44 : starHelperPair 20 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_45 : starHelperPair 20 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_46 : starHelperPair 20 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_47 : starHelperPair 20 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_48 : starHelperPair 20 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_49 : starHelperPair 20 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_50 : starHelperPair 20 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_51 : starHelperPair 20 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_52 : starHelperPair 20 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_53 : starHelperPair 20 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_54 : starHelperPair 20 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_55 : starHelperPair 20 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_56 : starHelperPair 20 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_57 : starHelperPair 20 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_58 : starHelperPair 20 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_59 : starHelperPair 20 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_60 : starHelperPair 20 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_61 : starHelperPair 20 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_62 : starHelperPair 20 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_20_63 : starHelperPair 20 63 = false := by
  decide +kernel

lemma starHelperRow_20 : starHelperRow 20 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_20_21, starHelperPair_20_23, starHelperPair_20_24, starHelperPair_20_26, starHelperPair_20_27, starHelperPair_20_28, starHelperPair_20_29, starHelperPair_20_30, starHelperPair_20_31, starHelperPair_20_33, starHelperPair_20_34, starHelperPair_20_35, starHelperPair_20_36, starHelperPair_20_38, starHelperPair_20_39, starHelperPair_20_40, starHelperPair_20_41, starHelperPair_20_43, starHelperPair_20_44, starHelperPair_20_45, starHelperPair_20_46, starHelperPair_20_47, starHelperPair_20_48, starHelperPair_20_49, starHelperPair_20_50, starHelperPair_20_51, starHelperPair_20_52, starHelperPair_20_53, starHelperPair_20_54, starHelperPair_20_55, starHelperPair_20_56, starHelperPair_20_57, starHelperPair_20_58, starHelperPair_20_59, starHelperPair_20_60, starHelperPair_20_61, starHelperPair_20_62, starHelperPair_20_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_23 : starHelperPair 21 23 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_24 : starHelperPair 21 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_26 : starHelperPair 21 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_27 : starHelperPair 21 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_28 : starHelperPair 21 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_29 : starHelperPair 21 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_30 : starHelperPair 21 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_31 : starHelperPair 21 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_33 : starHelperPair 21 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_34 : starHelperPair 21 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_35 : starHelperPair 21 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_36 : starHelperPair 21 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_38 : starHelperPair 21 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_39 : starHelperPair 21 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_40 : starHelperPair 21 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_41 : starHelperPair 21 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_43 : starHelperPair 21 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_44 : starHelperPair 21 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_45 : starHelperPair 21 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_46 : starHelperPair 21 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_47 : starHelperPair 21 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_48 : starHelperPair 21 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_49 : starHelperPair 21 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_50 : starHelperPair 21 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_51 : starHelperPair 21 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_52 : starHelperPair 21 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_53 : starHelperPair 21 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_54 : starHelperPair 21 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_55 : starHelperPair 21 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_56 : starHelperPair 21 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_57 : starHelperPair 21 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_58 : starHelperPair 21 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_59 : starHelperPair 21 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_60 : starHelperPair 21 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_61 : starHelperPair 21 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_62 : starHelperPair 21 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_21_63 : starHelperPair 21 63 = false := by
  decide +kernel

lemma starHelperRow_21 : starHelperRow 21 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_21_23, starHelperPair_21_24, starHelperPair_21_26, starHelperPair_21_27, starHelperPair_21_28, starHelperPair_21_29, starHelperPair_21_30, starHelperPair_21_31, starHelperPair_21_33, starHelperPair_21_34, starHelperPair_21_35, starHelperPair_21_36, starHelperPair_21_38, starHelperPair_21_39, starHelperPair_21_40, starHelperPair_21_41, starHelperPair_21_43, starHelperPair_21_44, starHelperPair_21_45, starHelperPair_21_46, starHelperPair_21_47, starHelperPair_21_48, starHelperPair_21_49, starHelperPair_21_50, starHelperPair_21_51, starHelperPair_21_52, starHelperPair_21_53, starHelperPair_21_54, starHelperPair_21_55, starHelperPair_21_56, starHelperPair_21_57, starHelperPair_21_58, starHelperPair_21_59, starHelperPair_21_60, starHelperPair_21_61, starHelperPair_21_62, starHelperPair_21_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_24 : starHelperPair 23 24 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_26 : starHelperPair 23 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_27 : starHelperPair 23 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_28 : starHelperPair 23 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_29 : starHelperPair 23 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_30 : starHelperPair 23 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_31 : starHelperPair 23 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_33 : starHelperPair 23 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_34 : starHelperPair 23 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_35 : starHelperPair 23 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_36 : starHelperPair 23 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_38 : starHelperPair 23 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_39 : starHelperPair 23 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_40 : starHelperPair 23 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_41 : starHelperPair 23 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_43 : starHelperPair 23 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_44 : starHelperPair 23 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_45 : starHelperPair 23 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_46 : starHelperPair 23 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_47 : starHelperPair 23 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_48 : starHelperPair 23 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_49 : starHelperPair 23 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_50 : starHelperPair 23 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_51 : starHelperPair 23 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_52 : starHelperPair 23 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_53 : starHelperPair 23 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_54 : starHelperPair 23 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_55 : starHelperPair 23 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_56 : starHelperPair 23 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_57 : starHelperPair 23 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_58 : starHelperPair 23 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_59 : starHelperPair 23 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_60 : starHelperPair 23 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_61 : starHelperPair 23 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_62 : starHelperPair 23 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_23_63 : starHelperPair 23 63 = false := by
  decide +kernel

lemma starHelperRow_23 : starHelperRow 23 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_23_24, starHelperPair_23_26, starHelperPair_23_27, starHelperPair_23_28, starHelperPair_23_29, starHelperPair_23_30, starHelperPair_23_31, starHelperPair_23_33, starHelperPair_23_34, starHelperPair_23_35, starHelperPair_23_36, starHelperPair_23_38, starHelperPair_23_39, starHelperPair_23_40, starHelperPair_23_41, starHelperPair_23_43, starHelperPair_23_44, starHelperPair_23_45, starHelperPair_23_46, starHelperPair_23_47, starHelperPair_23_48, starHelperPair_23_49, starHelperPair_23_50, starHelperPair_23_51, starHelperPair_23_52, starHelperPair_23_53, starHelperPair_23_54, starHelperPair_23_55, starHelperPair_23_56, starHelperPair_23_57, starHelperPair_23_58, starHelperPair_23_59, starHelperPair_23_60, starHelperPair_23_61, starHelperPair_23_62, starHelperPair_23_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_26 : starHelperPair 24 26 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_27 : starHelperPair 24 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_28 : starHelperPair 24 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_29 : starHelperPair 24 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_30 : starHelperPair 24 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_31 : starHelperPair 24 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_33 : starHelperPair 24 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_34 : starHelperPair 24 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_35 : starHelperPair 24 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_36 : starHelperPair 24 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_38 : starHelperPair 24 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_39 : starHelperPair 24 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_40 : starHelperPair 24 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_41 : starHelperPair 24 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_43 : starHelperPair 24 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_44 : starHelperPair 24 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_45 : starHelperPair 24 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_46 : starHelperPair 24 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_47 : starHelperPair 24 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_48 : starHelperPair 24 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_49 : starHelperPair 24 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_50 : starHelperPair 24 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_51 : starHelperPair 24 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_52 : starHelperPair 24 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_53 : starHelperPair 24 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_54 : starHelperPair 24 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_55 : starHelperPair 24 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_56 : starHelperPair 24 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_57 : starHelperPair 24 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_58 : starHelperPair 24 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_59 : starHelperPair 24 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_60 : starHelperPair 24 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_61 : starHelperPair 24 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_62 : starHelperPair 24 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_24_63 : starHelperPair 24 63 = false := by
  decide +kernel

lemma starHelperRow_24 : starHelperRow 24 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_24_26, starHelperPair_24_27, starHelperPair_24_28, starHelperPair_24_29, starHelperPair_24_30, starHelperPair_24_31, starHelperPair_24_33, starHelperPair_24_34, starHelperPair_24_35, starHelperPair_24_36, starHelperPair_24_38, starHelperPair_24_39, starHelperPair_24_40, starHelperPair_24_41, starHelperPair_24_43, starHelperPair_24_44, starHelperPair_24_45, starHelperPair_24_46, starHelperPair_24_47, starHelperPair_24_48, starHelperPair_24_49, starHelperPair_24_50, starHelperPair_24_51, starHelperPair_24_52, starHelperPair_24_53, starHelperPair_24_54, starHelperPair_24_55, starHelperPair_24_56, starHelperPair_24_57, starHelperPair_24_58, starHelperPair_24_59, starHelperPair_24_60, starHelperPair_24_61, starHelperPair_24_62, starHelperPair_24_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_27 : starHelperPair 26 27 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_28 : starHelperPair 26 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_29 : starHelperPair 26 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_30 : starHelperPair 26 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_31 : starHelperPair 26 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_33 : starHelperPair 26 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_34 : starHelperPair 26 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_35 : starHelperPair 26 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_36 : starHelperPair 26 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_38 : starHelperPair 26 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_39 : starHelperPair 26 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_40 : starHelperPair 26 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_41 : starHelperPair 26 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_43 : starHelperPair 26 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_44 : starHelperPair 26 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_45 : starHelperPair 26 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_46 : starHelperPair 26 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_47 : starHelperPair 26 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_48 : starHelperPair 26 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_49 : starHelperPair 26 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_50 : starHelperPair 26 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_51 : starHelperPair 26 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_52 : starHelperPair 26 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_53 : starHelperPair 26 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_54 : starHelperPair 26 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_55 : starHelperPair 26 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_56 : starHelperPair 26 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_57 : starHelperPair 26 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_58 : starHelperPair 26 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_59 : starHelperPair 26 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_60 : starHelperPair 26 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_61 : starHelperPair 26 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_62 : starHelperPair 26 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_26_63 : starHelperPair 26 63 = false := by
  decide +kernel

lemma starHelperRow_26 : starHelperRow 26 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_26_27, starHelperPair_26_28, starHelperPair_26_29, starHelperPair_26_30, starHelperPair_26_31, starHelperPair_26_33, starHelperPair_26_34, starHelperPair_26_35, starHelperPair_26_36, starHelperPair_26_38, starHelperPair_26_39, starHelperPair_26_40, starHelperPair_26_41, starHelperPair_26_43, starHelperPair_26_44, starHelperPair_26_45, starHelperPair_26_46, starHelperPair_26_47, starHelperPair_26_48, starHelperPair_26_49, starHelperPair_26_50, starHelperPair_26_51, starHelperPair_26_52, starHelperPair_26_53, starHelperPair_26_54, starHelperPair_26_55, starHelperPair_26_56, starHelperPair_26_57, starHelperPair_26_58, starHelperPair_26_59, starHelperPair_26_60, starHelperPair_26_61, starHelperPair_26_62, starHelperPair_26_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_28 : starHelperPair 27 28 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_29 : starHelperPair 27 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_30 : starHelperPair 27 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_31 : starHelperPair 27 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_33 : starHelperPair 27 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_34 : starHelperPair 27 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_35 : starHelperPair 27 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_36 : starHelperPair 27 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_38 : starHelperPair 27 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_39 : starHelperPair 27 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_40 : starHelperPair 27 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_41 : starHelperPair 27 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_43 : starHelperPair 27 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_44 : starHelperPair 27 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_45 : starHelperPair 27 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_46 : starHelperPair 27 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_47 : starHelperPair 27 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_48 : starHelperPair 27 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_49 : starHelperPair 27 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_50 : starHelperPair 27 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_51 : starHelperPair 27 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_52 : starHelperPair 27 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_53 : starHelperPair 27 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_54 : starHelperPair 27 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_55 : starHelperPair 27 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_56 : starHelperPair 27 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_57 : starHelperPair 27 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_58 : starHelperPair 27 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_59 : starHelperPair 27 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_60 : starHelperPair 27 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_61 : starHelperPair 27 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_62 : starHelperPair 27 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_27_63 : starHelperPair 27 63 = false := by
  decide +kernel

lemma starHelperRow_27 : starHelperRow 27 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_27_28, starHelperPair_27_29, starHelperPair_27_30, starHelperPair_27_31, starHelperPair_27_33, starHelperPair_27_34, starHelperPair_27_35, starHelperPair_27_36, starHelperPair_27_38, starHelperPair_27_39, starHelperPair_27_40, starHelperPair_27_41, starHelperPair_27_43, starHelperPair_27_44, starHelperPair_27_45, starHelperPair_27_46, starHelperPair_27_47, starHelperPair_27_48, starHelperPair_27_49, starHelperPair_27_50, starHelperPair_27_51, starHelperPair_27_52, starHelperPair_27_53, starHelperPair_27_54, starHelperPair_27_55, starHelperPair_27_56, starHelperPair_27_57, starHelperPair_27_58, starHelperPair_27_59, starHelperPair_27_60, starHelperPair_27_61, starHelperPair_27_62, starHelperPair_27_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_29 : starHelperPair 28 29 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_30 : starHelperPair 28 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_31 : starHelperPair 28 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_33 : starHelperPair 28 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_34 : starHelperPair 28 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_35 : starHelperPair 28 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_36 : starHelperPair 28 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_38 : starHelperPair 28 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_39 : starHelperPair 28 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_40 : starHelperPair 28 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_41 : starHelperPair 28 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_43 : starHelperPair 28 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_44 : starHelperPair 28 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_45 : starHelperPair 28 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_46 : starHelperPair 28 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_47 : starHelperPair 28 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_48 : starHelperPair 28 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_49 : starHelperPair 28 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_50 : starHelperPair 28 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_51 : starHelperPair 28 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_52 : starHelperPair 28 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_53 : starHelperPair 28 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_54 : starHelperPair 28 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_55 : starHelperPair 28 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_56 : starHelperPair 28 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_57 : starHelperPair 28 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_58 : starHelperPair 28 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_59 : starHelperPair 28 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_60 : starHelperPair 28 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_61 : starHelperPair 28 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_62 : starHelperPair 28 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_28_63 : starHelperPair 28 63 = false := by
  decide +kernel

lemma starHelperRow_28 : starHelperRow 28 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_28_29, starHelperPair_28_30, starHelperPair_28_31, starHelperPair_28_33, starHelperPair_28_34, starHelperPair_28_35, starHelperPair_28_36, starHelperPair_28_38, starHelperPair_28_39, starHelperPair_28_40, starHelperPair_28_41, starHelperPair_28_43, starHelperPair_28_44, starHelperPair_28_45, starHelperPair_28_46, starHelperPair_28_47, starHelperPair_28_48, starHelperPair_28_49, starHelperPair_28_50, starHelperPair_28_51, starHelperPair_28_52, starHelperPair_28_53, starHelperPair_28_54, starHelperPair_28_55, starHelperPair_28_56, starHelperPair_28_57, starHelperPair_28_58, starHelperPair_28_59, starHelperPair_28_60, starHelperPair_28_61, starHelperPair_28_62, starHelperPair_28_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_30 : starHelperPair 29 30 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_31 : starHelperPair 29 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_33 : starHelperPair 29 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_34 : starHelperPair 29 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_35 : starHelperPair 29 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_36 : starHelperPair 29 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_38 : starHelperPair 29 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_39 : starHelperPair 29 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_40 : starHelperPair 29 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_41 : starHelperPair 29 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_43 : starHelperPair 29 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_44 : starHelperPair 29 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_45 : starHelperPair 29 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_46 : starHelperPair 29 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_47 : starHelperPair 29 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_48 : starHelperPair 29 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_49 : starHelperPair 29 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_50 : starHelperPair 29 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_51 : starHelperPair 29 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_52 : starHelperPair 29 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_53 : starHelperPair 29 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_54 : starHelperPair 29 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_55 : starHelperPair 29 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_56 : starHelperPair 29 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_57 : starHelperPair 29 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_58 : starHelperPair 29 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_59 : starHelperPair 29 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_60 : starHelperPair 29 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_61 : starHelperPair 29 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_62 : starHelperPair 29 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_29_63 : starHelperPair 29 63 = false := by
  decide +kernel

lemma starHelperRow_29 : starHelperRow 29 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_29_30, starHelperPair_29_31, starHelperPair_29_33, starHelperPair_29_34, starHelperPair_29_35, starHelperPair_29_36, starHelperPair_29_38, starHelperPair_29_39, starHelperPair_29_40, starHelperPair_29_41, starHelperPair_29_43, starHelperPair_29_44, starHelperPair_29_45, starHelperPair_29_46, starHelperPair_29_47, starHelperPair_29_48, starHelperPair_29_49, starHelperPair_29_50, starHelperPair_29_51, starHelperPair_29_52, starHelperPair_29_53, starHelperPair_29_54, starHelperPair_29_55, starHelperPair_29_56, starHelperPair_29_57, starHelperPair_29_58, starHelperPair_29_59, starHelperPair_29_60, starHelperPair_29_61, starHelperPair_29_62, starHelperPair_29_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_31 : starHelperPair 30 31 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_33 : starHelperPair 30 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_34 : starHelperPair 30 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_35 : starHelperPair 30 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_36 : starHelperPair 30 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_38 : starHelperPair 30 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_39 : starHelperPair 30 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_40 : starHelperPair 30 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_41 : starHelperPair 30 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_43 : starHelperPair 30 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_44 : starHelperPair 30 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_45 : starHelperPair 30 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_46 : starHelperPair 30 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_47 : starHelperPair 30 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_48 : starHelperPair 30 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_49 : starHelperPair 30 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_50 : starHelperPair 30 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_51 : starHelperPair 30 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_52 : starHelperPair 30 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_53 : starHelperPair 30 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_54 : starHelperPair 30 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_55 : starHelperPair 30 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_56 : starHelperPair 30 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_57 : starHelperPair 30 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_58 : starHelperPair 30 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_59 : starHelperPair 30 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_60 : starHelperPair 30 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_61 : starHelperPair 30 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_62 : starHelperPair 30 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_30_63 : starHelperPair 30 63 = false := by
  decide +kernel

lemma starHelperRow_30 : starHelperRow 30 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_30_31, starHelperPair_30_33, starHelperPair_30_34, starHelperPair_30_35, starHelperPair_30_36, starHelperPair_30_38, starHelperPair_30_39, starHelperPair_30_40, starHelperPair_30_41, starHelperPair_30_43, starHelperPair_30_44, starHelperPair_30_45, starHelperPair_30_46, starHelperPair_30_47, starHelperPair_30_48, starHelperPair_30_49, starHelperPair_30_50, starHelperPair_30_51, starHelperPair_30_52, starHelperPair_30_53, starHelperPair_30_54, starHelperPair_30_55, starHelperPair_30_56, starHelperPair_30_57, starHelperPair_30_58, starHelperPair_30_59, starHelperPair_30_60, starHelperPair_30_61, starHelperPair_30_62, starHelperPair_30_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_33 : starHelperPair 31 33 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_34 : starHelperPair 31 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_35 : starHelperPair 31 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_36 : starHelperPair 31 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_38 : starHelperPair 31 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_39 : starHelperPair 31 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_40 : starHelperPair 31 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_41 : starHelperPair 31 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_43 : starHelperPair 31 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_44 : starHelperPair 31 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_45 : starHelperPair 31 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_46 : starHelperPair 31 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_47 : starHelperPair 31 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_48 : starHelperPair 31 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_49 : starHelperPair 31 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_50 : starHelperPair 31 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_51 : starHelperPair 31 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_52 : starHelperPair 31 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_53 : starHelperPair 31 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_54 : starHelperPair 31 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_55 : starHelperPair 31 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_56 : starHelperPair 31 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_57 : starHelperPair 31 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_58 : starHelperPair 31 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_59 : starHelperPair 31 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_60 : starHelperPair 31 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_61 : starHelperPair 31 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_62 : starHelperPair 31 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_31_63 : starHelperPair 31 63 = false := by
  decide +kernel

lemma starHelperRow_31 : starHelperRow 31 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_31_33, starHelperPair_31_34, starHelperPair_31_35, starHelperPair_31_36, starHelperPair_31_38, starHelperPair_31_39, starHelperPair_31_40, starHelperPair_31_41, starHelperPair_31_43, starHelperPair_31_44, starHelperPair_31_45, starHelperPair_31_46, starHelperPair_31_47, starHelperPair_31_48, starHelperPair_31_49, starHelperPair_31_50, starHelperPair_31_51, starHelperPair_31_52, starHelperPair_31_53, starHelperPair_31_54, starHelperPair_31_55, starHelperPair_31_56, starHelperPair_31_57, starHelperPair_31_58, starHelperPair_31_59, starHelperPair_31_60, starHelperPair_31_61, starHelperPair_31_62, starHelperPair_31_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_34 : starHelperPair 33 34 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_35 : starHelperPair 33 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_36 : starHelperPair 33 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_38 : starHelperPair 33 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_39 : starHelperPair 33 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_40 : starHelperPair 33 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_41 : starHelperPair 33 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_43 : starHelperPair 33 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_44 : starHelperPair 33 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_45 : starHelperPair 33 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_46 : starHelperPair 33 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_47 : starHelperPair 33 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_48 : starHelperPair 33 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_49 : starHelperPair 33 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_50 : starHelperPair 33 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_51 : starHelperPair 33 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_52 : starHelperPair 33 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_53 : starHelperPair 33 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_54 : starHelperPair 33 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_55 : starHelperPair 33 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_56 : starHelperPair 33 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_57 : starHelperPair 33 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_58 : starHelperPair 33 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_59 : starHelperPair 33 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_60 : starHelperPair 33 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_61 : starHelperPair 33 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_62 : starHelperPair 33 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_33_63 : starHelperPair 33 63 = false := by
  decide +kernel

lemma starHelperRow_33 : starHelperRow 33 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_33_34, starHelperPair_33_35, starHelperPair_33_36, starHelperPair_33_38, starHelperPair_33_39, starHelperPair_33_40, starHelperPair_33_41, starHelperPair_33_43, starHelperPair_33_44, starHelperPair_33_45, starHelperPair_33_46, starHelperPair_33_47, starHelperPair_33_48, starHelperPair_33_49, starHelperPair_33_50, starHelperPair_33_51, starHelperPair_33_52, starHelperPair_33_53, starHelperPair_33_54, starHelperPair_33_55, starHelperPair_33_56, starHelperPair_33_57, starHelperPair_33_58, starHelperPair_33_59, starHelperPair_33_60, starHelperPair_33_61, starHelperPair_33_62, starHelperPair_33_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_35 : starHelperPair 34 35 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_36 : starHelperPair 34 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_38 : starHelperPair 34 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_39 : starHelperPair 34 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_40 : starHelperPair 34 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_41 : starHelperPair 34 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_43 : starHelperPair 34 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_44 : starHelperPair 34 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_45 : starHelperPair 34 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_46 : starHelperPair 34 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_47 : starHelperPair 34 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_48 : starHelperPair 34 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_49 : starHelperPair 34 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_50 : starHelperPair 34 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_51 : starHelperPair 34 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_52 : starHelperPair 34 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_53 : starHelperPair 34 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_54 : starHelperPair 34 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_55 : starHelperPair 34 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_56 : starHelperPair 34 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_57 : starHelperPair 34 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_58 : starHelperPair 34 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_59 : starHelperPair 34 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_60 : starHelperPair 34 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_61 : starHelperPair 34 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_62 : starHelperPair 34 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_34_63 : starHelperPair 34 63 = false := by
  decide +kernel

lemma starHelperRow_34 : starHelperRow 34 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_34_35, starHelperPair_34_36, starHelperPair_34_38, starHelperPair_34_39, starHelperPair_34_40, starHelperPair_34_41, starHelperPair_34_43, starHelperPair_34_44, starHelperPair_34_45, starHelperPair_34_46, starHelperPair_34_47, starHelperPair_34_48, starHelperPair_34_49, starHelperPair_34_50, starHelperPair_34_51, starHelperPair_34_52, starHelperPair_34_53, starHelperPair_34_54, starHelperPair_34_55, starHelperPair_34_56, starHelperPair_34_57, starHelperPair_34_58, starHelperPair_34_59, starHelperPair_34_60, starHelperPair_34_61, starHelperPair_34_62, starHelperPair_34_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_36 : starHelperPair 35 36 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_38 : starHelperPair 35 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_39 : starHelperPair 35 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_40 : starHelperPair 35 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_41 : starHelperPair 35 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_43 : starHelperPair 35 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_44 : starHelperPair 35 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_45 : starHelperPair 35 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_46 : starHelperPair 35 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_47 : starHelperPair 35 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_48 : starHelperPair 35 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_49 : starHelperPair 35 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_50 : starHelperPair 35 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_51 : starHelperPair 35 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_52 : starHelperPair 35 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_53 : starHelperPair 35 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_54 : starHelperPair 35 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_55 : starHelperPair 35 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_56 : starHelperPair 35 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_57 : starHelperPair 35 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_58 : starHelperPair 35 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_59 : starHelperPair 35 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_60 : starHelperPair 35 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_61 : starHelperPair 35 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_62 : starHelperPair 35 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_35_63 : starHelperPair 35 63 = false := by
  decide +kernel

lemma starHelperRow_35 : starHelperRow 35 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_35_36, starHelperPair_35_38, starHelperPair_35_39, starHelperPair_35_40, starHelperPair_35_41, starHelperPair_35_43, starHelperPair_35_44, starHelperPair_35_45, starHelperPair_35_46, starHelperPair_35_47, starHelperPair_35_48, starHelperPair_35_49, starHelperPair_35_50, starHelperPair_35_51, starHelperPair_35_52, starHelperPair_35_53, starHelperPair_35_54, starHelperPair_35_55, starHelperPair_35_56, starHelperPair_35_57, starHelperPair_35_58, starHelperPair_35_59, starHelperPair_35_60, starHelperPair_35_61, starHelperPair_35_62, starHelperPair_35_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_38 : starHelperPair 36 38 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_39 : starHelperPair 36 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_40 : starHelperPair 36 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_41 : starHelperPair 36 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_43 : starHelperPair 36 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_44 : starHelperPair 36 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_45 : starHelperPair 36 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_46 : starHelperPair 36 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_47 : starHelperPair 36 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_48 : starHelperPair 36 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_49 : starHelperPair 36 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_50 : starHelperPair 36 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_51 : starHelperPair 36 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_52 : starHelperPair 36 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_53 : starHelperPair 36 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_54 : starHelperPair 36 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_55 : starHelperPair 36 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_56 : starHelperPair 36 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_57 : starHelperPair 36 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_58 : starHelperPair 36 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_59 : starHelperPair 36 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_60 : starHelperPair 36 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_61 : starHelperPair 36 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_62 : starHelperPair 36 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_36_63 : starHelperPair 36 63 = false := by
  decide +kernel

lemma starHelperRow_36 : starHelperRow 36 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_36_38, starHelperPair_36_39, starHelperPair_36_40, starHelperPair_36_41, starHelperPair_36_43, starHelperPair_36_44, starHelperPair_36_45, starHelperPair_36_46, starHelperPair_36_47, starHelperPair_36_48, starHelperPair_36_49, starHelperPair_36_50, starHelperPair_36_51, starHelperPair_36_52, starHelperPair_36_53, starHelperPair_36_54, starHelperPair_36_55, starHelperPair_36_56, starHelperPair_36_57, starHelperPair_36_58, starHelperPair_36_59, starHelperPair_36_60, starHelperPair_36_61, starHelperPair_36_62, starHelperPair_36_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_39 : starHelperPair 38 39 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_40 : starHelperPair 38 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_41 : starHelperPair 38 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_43 : starHelperPair 38 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_44 : starHelperPair 38 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_45 : starHelperPair 38 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_46 : starHelperPair 38 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_47 : starHelperPair 38 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_48 : starHelperPair 38 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_49 : starHelperPair 38 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_50 : starHelperPair 38 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_51 : starHelperPair 38 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_52 : starHelperPair 38 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_53 : starHelperPair 38 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_54 : starHelperPair 38 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_55 : starHelperPair 38 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_56 : starHelperPair 38 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_57 : starHelperPair 38 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_58 : starHelperPair 38 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_59 : starHelperPair 38 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_60 : starHelperPair 38 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_61 : starHelperPair 38 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_62 : starHelperPair 38 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_38_63 : starHelperPair 38 63 = false := by
  decide +kernel

lemma starHelperRow_38 : starHelperRow 38 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_38_39, starHelperPair_38_40, starHelperPair_38_41, starHelperPair_38_43, starHelperPair_38_44, starHelperPair_38_45, starHelperPair_38_46, starHelperPair_38_47, starHelperPair_38_48, starHelperPair_38_49, starHelperPair_38_50, starHelperPair_38_51, starHelperPair_38_52, starHelperPair_38_53, starHelperPair_38_54, starHelperPair_38_55, starHelperPair_38_56, starHelperPair_38_57, starHelperPair_38_58, starHelperPair_38_59, starHelperPair_38_60, starHelperPair_38_61, starHelperPair_38_62, starHelperPair_38_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_40 : starHelperPair 39 40 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_41 : starHelperPair 39 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_43 : starHelperPair 39 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_44 : starHelperPair 39 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_45 : starHelperPair 39 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_46 : starHelperPair 39 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_47 : starHelperPair 39 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_48 : starHelperPair 39 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_49 : starHelperPair 39 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_50 : starHelperPair 39 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_51 : starHelperPair 39 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_52 : starHelperPair 39 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_53 : starHelperPair 39 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_54 : starHelperPair 39 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_55 : starHelperPair 39 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_56 : starHelperPair 39 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_57 : starHelperPair 39 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_58 : starHelperPair 39 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_59 : starHelperPair 39 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_60 : starHelperPair 39 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_61 : starHelperPair 39 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_62 : starHelperPair 39 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_39_63 : starHelperPair 39 63 = false := by
  decide +kernel

lemma starHelperRow_39 : starHelperRow 39 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_39_40, starHelperPair_39_41, starHelperPair_39_43, starHelperPair_39_44, starHelperPair_39_45, starHelperPair_39_46, starHelperPair_39_47, starHelperPair_39_48, starHelperPair_39_49, starHelperPair_39_50, starHelperPair_39_51, starHelperPair_39_52, starHelperPair_39_53, starHelperPair_39_54, starHelperPair_39_55, starHelperPair_39_56, starHelperPair_39_57, starHelperPair_39_58, starHelperPair_39_59, starHelperPair_39_60, starHelperPair_39_61, starHelperPair_39_62, starHelperPair_39_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_41 : starHelperPair 40 41 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_43 : starHelperPair 40 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_44 : starHelperPair 40 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_45 : starHelperPair 40 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_46 : starHelperPair 40 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_47 : starHelperPair 40 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_48 : starHelperPair 40 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_49 : starHelperPair 40 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_50 : starHelperPair 40 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_51 : starHelperPair 40 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_52 : starHelperPair 40 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_53 : starHelperPair 40 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_54 : starHelperPair 40 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_55 : starHelperPair 40 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_56 : starHelperPair 40 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_57 : starHelperPair 40 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_58 : starHelperPair 40 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_59 : starHelperPair 40 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_60 : starHelperPair 40 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_61 : starHelperPair 40 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_62 : starHelperPair 40 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_40_63 : starHelperPair 40 63 = false := by
  decide +kernel

lemma starHelperRow_40 : starHelperRow 40 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_40_41, starHelperPair_40_43, starHelperPair_40_44, starHelperPair_40_45, starHelperPair_40_46, starHelperPair_40_47, starHelperPair_40_48, starHelperPair_40_49, starHelperPair_40_50, starHelperPair_40_51, starHelperPair_40_52, starHelperPair_40_53, starHelperPair_40_54, starHelperPair_40_55, starHelperPair_40_56, starHelperPair_40_57, starHelperPair_40_58, starHelperPair_40_59, starHelperPair_40_60, starHelperPair_40_61, starHelperPair_40_62, starHelperPair_40_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_43 : starHelperPair 41 43 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_44 : starHelperPair 41 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_45 : starHelperPair 41 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_46 : starHelperPair 41 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_47 : starHelperPair 41 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_48 : starHelperPair 41 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_49 : starHelperPair 41 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_50 : starHelperPair 41 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_51 : starHelperPair 41 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_52 : starHelperPair 41 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_53 : starHelperPair 41 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_54 : starHelperPair 41 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_55 : starHelperPair 41 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_56 : starHelperPair 41 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_57 : starHelperPair 41 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_58 : starHelperPair 41 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_59 : starHelperPair 41 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_60 : starHelperPair 41 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_61 : starHelperPair 41 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_62 : starHelperPair 41 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_41_63 : starHelperPair 41 63 = false := by
  decide +kernel

lemma starHelperRow_41 : starHelperRow 41 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_41_43, starHelperPair_41_44, starHelperPair_41_45, starHelperPair_41_46, starHelperPair_41_47, starHelperPair_41_48, starHelperPair_41_49, starHelperPair_41_50, starHelperPair_41_51, starHelperPair_41_52, starHelperPair_41_53, starHelperPair_41_54, starHelperPair_41_55, starHelperPair_41_56, starHelperPair_41_57, starHelperPair_41_58, starHelperPair_41_59, starHelperPair_41_60, starHelperPair_41_61, starHelperPair_41_62, starHelperPair_41_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_44 : starHelperPair 43 44 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_45 : starHelperPair 43 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_46 : starHelperPair 43 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_47 : starHelperPair 43 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_48 : starHelperPair 43 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_49 : starHelperPair 43 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_50 : starHelperPair 43 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_51 : starHelperPair 43 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_52 : starHelperPair 43 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_53 : starHelperPair 43 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_54 : starHelperPair 43 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_55 : starHelperPair 43 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_56 : starHelperPair 43 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_57 : starHelperPair 43 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_58 : starHelperPair 43 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_59 : starHelperPair 43 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_60 : starHelperPair 43 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_61 : starHelperPair 43 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_62 : starHelperPair 43 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_43_63 : starHelperPair 43 63 = false := by
  decide +kernel

lemma starHelperRow_43 : starHelperRow 43 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_43_44, starHelperPair_43_45, starHelperPair_43_46, starHelperPair_43_47, starHelperPair_43_48, starHelperPair_43_49, starHelperPair_43_50, starHelperPair_43_51, starHelperPair_43_52, starHelperPair_43_53, starHelperPair_43_54, starHelperPair_43_55, starHelperPair_43_56, starHelperPair_43_57, starHelperPair_43_58, starHelperPair_43_59, starHelperPair_43_60, starHelperPair_43_61, starHelperPair_43_62, starHelperPair_43_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_45 : starHelperPair 44 45 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_46 : starHelperPair 44 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_47 : starHelperPair 44 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_48 : starHelperPair 44 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_49 : starHelperPair 44 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_50 : starHelperPair 44 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_51 : starHelperPair 44 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_52 : starHelperPair 44 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_53 : starHelperPair 44 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_54 : starHelperPair 44 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_55 : starHelperPair 44 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_56 : starHelperPair 44 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_57 : starHelperPair 44 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_58 : starHelperPair 44 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_59 : starHelperPair 44 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_60 : starHelperPair 44 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_61 : starHelperPair 44 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_62 : starHelperPair 44 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_44_63 : starHelperPair 44 63 = false := by
  decide +kernel

lemma starHelperRow_44 : starHelperRow 44 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_44_45, starHelperPair_44_46, starHelperPair_44_47, starHelperPair_44_48, starHelperPair_44_49, starHelperPair_44_50, starHelperPair_44_51, starHelperPair_44_52, starHelperPair_44_53, starHelperPair_44_54, starHelperPair_44_55, starHelperPair_44_56, starHelperPair_44_57, starHelperPair_44_58, starHelperPair_44_59, starHelperPair_44_60, starHelperPair_44_61, starHelperPair_44_62, starHelperPair_44_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_46 : starHelperPair 45 46 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_47 : starHelperPair 45 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_48 : starHelperPair 45 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_49 : starHelperPair 45 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_50 : starHelperPair 45 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_51 : starHelperPair 45 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_52 : starHelperPair 45 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_53 : starHelperPair 45 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_54 : starHelperPair 45 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_55 : starHelperPair 45 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_56 : starHelperPair 45 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_57 : starHelperPair 45 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_58 : starHelperPair 45 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_59 : starHelperPair 45 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_60 : starHelperPair 45 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_61 : starHelperPair 45 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_62 : starHelperPair 45 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_45_63 : starHelperPair 45 63 = false := by
  decide +kernel

lemma starHelperRow_45 : starHelperRow 45 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_45_46, starHelperPair_45_47, starHelperPair_45_48, starHelperPair_45_49, starHelperPair_45_50, starHelperPair_45_51, starHelperPair_45_52, starHelperPair_45_53, starHelperPair_45_54, starHelperPair_45_55, starHelperPair_45_56, starHelperPair_45_57, starHelperPair_45_58, starHelperPair_45_59, starHelperPair_45_60, starHelperPair_45_61, starHelperPair_45_62, starHelperPair_45_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_47 : starHelperPair 46 47 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_48 : starHelperPair 46 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_49 : starHelperPair 46 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_50 : starHelperPair 46 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_51 : starHelperPair 46 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_52 : starHelperPair 46 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_53 : starHelperPair 46 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_54 : starHelperPair 46 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_55 : starHelperPair 46 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_56 : starHelperPair 46 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_57 : starHelperPair 46 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_58 : starHelperPair 46 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_59 : starHelperPair 46 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_60 : starHelperPair 46 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_61 : starHelperPair 46 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_62 : starHelperPair 46 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_46_63 : starHelperPair 46 63 = false := by
  decide +kernel

lemma starHelperRow_46 : starHelperRow 46 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_46_47, starHelperPair_46_48, starHelperPair_46_49, starHelperPair_46_50, starHelperPair_46_51, starHelperPair_46_52, starHelperPair_46_53, starHelperPair_46_54, starHelperPair_46_55, starHelperPair_46_56, starHelperPair_46_57, starHelperPair_46_58, starHelperPair_46_59, starHelperPair_46_60, starHelperPair_46_61, starHelperPair_46_62, starHelperPair_46_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_48 : starHelperPair 47 48 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_49 : starHelperPair 47 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_50 : starHelperPair 47 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_51 : starHelperPair 47 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_52 : starHelperPair 47 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_53 : starHelperPair 47 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_54 : starHelperPair 47 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_55 : starHelperPair 47 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_56 : starHelperPair 47 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_57 : starHelperPair 47 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_58 : starHelperPair 47 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_59 : starHelperPair 47 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_60 : starHelperPair 47 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_61 : starHelperPair 47 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_62 : starHelperPair 47 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_47_63 : starHelperPair 47 63 = false := by
  decide +kernel

lemma starHelperRow_47 : starHelperRow 47 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_47_48, starHelperPair_47_49, starHelperPair_47_50, starHelperPair_47_51, starHelperPair_47_52, starHelperPair_47_53, starHelperPair_47_54, starHelperPair_47_55, starHelperPair_47_56, starHelperPair_47_57, starHelperPair_47_58, starHelperPair_47_59, starHelperPair_47_60, starHelperPair_47_61, starHelperPair_47_62, starHelperPair_47_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_49 : starHelperPair 48 49 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_50 : starHelperPair 48 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_51 : starHelperPair 48 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_52 : starHelperPair 48 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_53 : starHelperPair 48 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_54 : starHelperPair 48 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_55 : starHelperPair 48 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_56 : starHelperPair 48 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_57 : starHelperPair 48 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_58 : starHelperPair 48 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_59 : starHelperPair 48 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_60 : starHelperPair 48 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_61 : starHelperPair 48 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_62 : starHelperPair 48 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_48_63 : starHelperPair 48 63 = false := by
  decide +kernel

lemma starHelperRow_48 : starHelperRow 48 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_48_49, starHelperPair_48_50, starHelperPair_48_51, starHelperPair_48_52, starHelperPair_48_53, starHelperPair_48_54, starHelperPair_48_55, starHelperPair_48_56, starHelperPair_48_57, starHelperPair_48_58, starHelperPair_48_59, starHelperPair_48_60, starHelperPair_48_61, starHelperPair_48_62, starHelperPair_48_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_50 : starHelperPair 49 50 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_51 : starHelperPair 49 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_52 : starHelperPair 49 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_53 : starHelperPair 49 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_54 : starHelperPair 49 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_55 : starHelperPair 49 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_56 : starHelperPair 49 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_57 : starHelperPair 49 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_58 : starHelperPair 49 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_59 : starHelperPair 49 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_60 : starHelperPair 49 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_61 : starHelperPair 49 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_62 : starHelperPair 49 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_49_63 : starHelperPair 49 63 = false := by
  decide +kernel

lemma starHelperRow_49 : starHelperRow 49 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_49_50, starHelperPair_49_51, starHelperPair_49_52, starHelperPair_49_53, starHelperPair_49_54, starHelperPair_49_55, starHelperPair_49_56, starHelperPair_49_57, starHelperPair_49_58, starHelperPair_49_59, starHelperPair_49_60, starHelperPair_49_61, starHelperPair_49_62, starHelperPair_49_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_51 : starHelperPair 50 51 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_52 : starHelperPair 50 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_53 : starHelperPair 50 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_54 : starHelperPair 50 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_55 : starHelperPair 50 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_56 : starHelperPair 50 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_57 : starHelperPair 50 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_58 : starHelperPair 50 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_59 : starHelperPair 50 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_60 : starHelperPair 50 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_61 : starHelperPair 50 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_62 : starHelperPair 50 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_50_63 : starHelperPair 50 63 = false := by
  decide +kernel

lemma starHelperRow_50 : starHelperRow 50 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_50_51, starHelperPair_50_52, starHelperPair_50_53, starHelperPair_50_54, starHelperPair_50_55, starHelperPair_50_56, starHelperPair_50_57, starHelperPair_50_58, starHelperPair_50_59, starHelperPair_50_60, starHelperPair_50_61, starHelperPair_50_62, starHelperPair_50_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_52 : starHelperPair 51 52 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_53 : starHelperPair 51 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_54 : starHelperPair 51 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_55 : starHelperPair 51 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_56 : starHelperPair 51 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_57 : starHelperPair 51 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_58 : starHelperPair 51 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_59 : starHelperPair 51 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_60 : starHelperPair 51 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_61 : starHelperPair 51 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_62 : starHelperPair 51 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_51_63 : starHelperPair 51 63 = false := by
  decide +kernel

lemma starHelperRow_51 : starHelperRow 51 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_51_52, starHelperPair_51_53, starHelperPair_51_54, starHelperPair_51_55, starHelperPair_51_56, starHelperPair_51_57, starHelperPair_51_58, starHelperPair_51_59, starHelperPair_51_60, starHelperPair_51_61, starHelperPair_51_62, starHelperPair_51_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_53 : starHelperPair 52 53 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_54 : starHelperPair 52 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_55 : starHelperPair 52 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_56 : starHelperPair 52 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_57 : starHelperPair 52 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_58 : starHelperPair 52 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_59 : starHelperPair 52 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_60 : starHelperPair 52 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_61 : starHelperPair 52 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_62 : starHelperPair 52 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_52_63 : starHelperPair 52 63 = false := by
  decide +kernel

lemma starHelperRow_52 : starHelperRow 52 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_52_53, starHelperPair_52_54, starHelperPair_52_55, starHelperPair_52_56, starHelperPair_52_57, starHelperPair_52_58, starHelperPair_52_59, starHelperPair_52_60, starHelperPair_52_61, starHelperPair_52_62, starHelperPair_52_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_54 : starHelperPair 53 54 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_55 : starHelperPair 53 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_56 : starHelperPair 53 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_57 : starHelperPair 53 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_58 : starHelperPair 53 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_59 : starHelperPair 53 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_60 : starHelperPair 53 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_61 : starHelperPair 53 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_62 : starHelperPair 53 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_53_63 : starHelperPair 53 63 = false := by
  decide +kernel

lemma starHelperRow_53 : starHelperRow 53 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_53_54, starHelperPair_53_55, starHelperPair_53_56, starHelperPair_53_57, starHelperPair_53_58, starHelperPair_53_59, starHelperPair_53_60, starHelperPair_53_61, starHelperPair_53_62, starHelperPair_53_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_55 : starHelperPair 54 55 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_56 : starHelperPair 54 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_57 : starHelperPair 54 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_58 : starHelperPair 54 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_59 : starHelperPair 54 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_60 : starHelperPair 54 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_61 : starHelperPair 54 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_62 : starHelperPair 54 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_54_63 : starHelperPair 54 63 = false := by
  decide +kernel

lemma starHelperRow_54 : starHelperRow 54 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_54_55, starHelperPair_54_56, starHelperPair_54_57, starHelperPair_54_58, starHelperPair_54_59, starHelperPair_54_60, starHelperPair_54_61, starHelperPair_54_62, starHelperPair_54_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_56 : starHelperPair 55 56 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_57 : starHelperPair 55 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_58 : starHelperPair 55 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_59 : starHelperPair 55 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_60 : starHelperPair 55 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_61 : starHelperPair 55 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_62 : starHelperPair 55 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_55_63 : starHelperPair 55 63 = false := by
  decide +kernel

lemma starHelperRow_55 : starHelperRow 55 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_55_56, starHelperPair_55_57, starHelperPair_55_58, starHelperPair_55_59, starHelperPair_55_60, starHelperPair_55_61, starHelperPair_55_62, starHelperPair_55_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_57 : starHelperPair 56 57 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_58 : starHelperPair 56 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_59 : starHelperPair 56 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_60 : starHelperPair 56 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_61 : starHelperPair 56 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_62 : starHelperPair 56 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_56_63 : starHelperPair 56 63 = false := by
  decide +kernel

lemma starHelperRow_56 : starHelperRow 56 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_56_57, starHelperPair_56_58, starHelperPair_56_59, starHelperPair_56_60, starHelperPair_56_61, starHelperPair_56_62, starHelperPair_56_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_57_58 : starHelperPair 57 58 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_57_59 : starHelperPair 57 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_57_60 : starHelperPair 57 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_57_61 : starHelperPair 57 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_57_62 : starHelperPair 57 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_57_63 : starHelperPair 57 63 = false := by
  decide +kernel

lemma starHelperRow_57 : starHelperRow 57 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_57_58, starHelperPair_57_59, starHelperPair_57_60, starHelperPair_57_61, starHelperPair_57_62, starHelperPair_57_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_58_59 : starHelperPair 58 59 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_58_60 : starHelperPair 58 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_58_61 : starHelperPair 58 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_58_62 : starHelperPair 58 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_58_63 : starHelperPair 58 63 = false := by
  decide +kernel

lemma starHelperRow_58 : starHelperRow 58 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_58_59, starHelperPair_58_60, starHelperPair_58_61, starHelperPair_58_62, starHelperPair_58_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_59_60 : starHelperPair 59 60 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_59_61 : starHelperPair 59 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_59_62 : starHelperPair 59 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_59_63 : starHelperPair 59 63 = false := by
  decide +kernel

lemma starHelperRow_59 : starHelperRow 59 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_59_60, starHelperPair_59_61, starHelperPair_59_62, starHelperPair_59_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_60_61 : starHelperPair 60 61 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_60_62 : starHelperPair 60 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_60_63 : starHelperPair 60 63 = false := by
  decide +kernel

lemma starHelperRow_60 : starHelperRow 60 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_60_61, starHelperPair_60_62, starHelperPair_60_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_61_62 : starHelperPair 61 62 = false := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_61_63 : starHelperPair 61 63 = false := by
  decide +kernel

lemma starHelperRow_61 : starHelperRow 61 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_61_62, starHelperPair_61_63]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperPair_62_63 : starHelperPair 62 63 = false := by
  decide +kernel

lemma starHelperRow_62 : starHelperRow 62 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or,
    starHelperPair_62_63]

lemma starHelperRow_63 : starHelperRow 63 = false := by
  simp only [starHelperRow, helperMasks, List.any_cons, List.any_nil,
    Nat.reduceLT, ite_true, ite_false, Bool.false_or]

lemma starHelperSearch_false : starHelperSearch = false := by
  simp only [starHelperSearch, helperMasks, List.any_cons, List.any_nil,
    Bool.false_or, starHelperRow_3, starHelperRow_5, starHelperRow_6, starHelperRow_7, starHelperRow_9, starHelperRow_10, starHelperRow_11, starHelperRow_12, starHelperRow_13, starHelperRow_14, starHelperRow_15, starHelperRow_17, starHelperRow_18, starHelperRow_19, starHelperRow_20, starHelperRow_21, starHelperRow_23, starHelperRow_24, starHelperRow_26, starHelperRow_27, starHelperRow_28, starHelperRow_29, starHelperRow_30, starHelperRow_31, starHelperRow_33, starHelperRow_34, starHelperRow_35, starHelperRow_36, starHelperRow_38, starHelperRow_39, starHelperRow_40, starHelperRow_41, starHelperRow_43, starHelperRow_44, starHelperRow_45, starHelperRow_46, starHelperRow_47, starHelperRow_48, starHelperRow_49, starHelperRow_50, starHelperRow_51, starHelperRow_52, starHelperRow_53, starHelperRow_54, starHelperRow_55, starHelperRow_56, starHelperRow_57, starHelperRow_58, starHelperRow_59, starHelperRow_60, starHelperRow_61, starHelperRow_62, starHelperRow_63]

end PEqualNP.Outside.L_meta_2592
