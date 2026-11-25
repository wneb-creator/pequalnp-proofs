import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592

def starMasks : List ℕ := [22, 37, 25, 42]

def singletonMasks : List ℕ := [1, 2, 4, 8, 16, 32]

def helperMasks : List ℕ :=
  [3, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 23, 24, 26, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 39, 40, 41, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

lemma helperMasks_spec : helperMasks =
    (List.range 64).filter (fun x =>
      x != 0 && Nat.land x (x - 1) != 0 && !(starMasks.contains x)) := by
  decide

def setStepAllowed (known : List ℕ) (target : ℕ) : Bool :=
  known.any fun a => Nat.land target a == target ||
    known.any fun b => Nat.lor a b == target

def closeStarStep (known : List ℕ) (target : ℕ) : List ℕ :=
  if known.contains target then known
  else if setStepAllowed known target then target :: known else known

def closeStarSets : ℕ → List ℕ → List ℕ → List ℕ
  | 0, _, known => known
  | fuel + 1, allowed, known =>
    let next := allowed.foldl closeStarStep known
    if next.length == known.length then known
    else closeStarSets fuel allowed next

def starTripleSucceeds (a b c : ℕ) : Bool :=
  let known := closeStarSets 7 (starMasks ++ [a, b, c]) singletonMasks
  starMasks.all known.contains

def starHelperRow (a : ℕ) : Bool :=
  helperMasks.any fun b =>
    if a < b then helperMasks.any fun c =>
      if b < c then starTripleSucceeds a b c else false
    else false

def starHelperSearch : Bool := helperMasks.any starHelperRow

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_3 : starHelperRow 3 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_5 : starHelperRow 5 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_6 : starHelperRow 6 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_7 : starHelperRow 7 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_9 : starHelperRow 9 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_10 : starHelperRow 10 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_11 : starHelperRow 11 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_12 : starHelperRow 12 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_13 : starHelperRow 13 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_14 : starHelperRow 14 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_15 : starHelperRow 15 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_17 : starHelperRow 17 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_18 : starHelperRow 18 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_19 : starHelperRow 19 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_20 : starHelperRow 20 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_21 : starHelperRow 21 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_23 : starHelperRow 23 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_24 : starHelperRow 24 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_26 : starHelperRow 26 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_27 : starHelperRow 27 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_28 : starHelperRow 28 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_29 : starHelperRow 29 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_30 : starHelperRow 30 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_31 : starHelperRow 31 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_33 : starHelperRow 33 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_34 : starHelperRow 34 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_35 : starHelperRow 35 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_36 : starHelperRow 36 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_38 : starHelperRow 38 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_39 : starHelperRow 39 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_40 : starHelperRow 40 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_41 : starHelperRow 41 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_43 : starHelperRow 43 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_44 : starHelperRow 44 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_45 : starHelperRow 45 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_46 : starHelperRow 46 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_47 : starHelperRow 47 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_48 : starHelperRow 48 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_49 : starHelperRow 49 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_50 : starHelperRow 50 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_51 : starHelperRow 51 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_52 : starHelperRow 52 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_53 : starHelperRow 53 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_54 : starHelperRow 54 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_55 : starHelperRow 55 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_56 : starHelperRow 56 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_57 : starHelperRow 57 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_58 : starHelperRow 58 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_59 : starHelperRow 59 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_60 : starHelperRow 60 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_61 : starHelperRow 61 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_62 : starHelperRow 62 = false := by
  decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma starHelperRow_63 : starHelperRow 63 = false := by
  decide

lemma starHelperSearch_false : starHelperSearch = false := by
  simp only [starHelperSearch, helperMasks, List.any_cons, List.any_nil,
    starHelperRow_3,
    starHelperRow_5,
    starHelperRow_6,
    starHelperRow_7,
    starHelperRow_9,
    starHelperRow_10,
    starHelperRow_11,
    starHelperRow_12,
    starHelperRow_13,
    starHelperRow_14,
    starHelperRow_15,
    starHelperRow_17,
    starHelperRow_18,
    starHelperRow_19,
    starHelperRow_20,
    starHelperRow_21,
    starHelperRow_23,
    starHelperRow_24,
    starHelperRow_26,
    starHelperRow_27,
    starHelperRow_28,
    starHelperRow_29,
    starHelperRow_30,
    starHelperRow_31,
    starHelperRow_33,
    starHelperRow_34,
    starHelperRow_35,
    starHelperRow_36,
    starHelperRow_38,
    starHelperRow_39,
    starHelperRow_40,
    starHelperRow_41,
    starHelperRow_43,
    starHelperRow_44,
    starHelperRow_45,
    starHelperRow_46,
    starHelperRow_47,
    starHelperRow_48,
    starHelperRow_49,
    starHelperRow_50,
    starHelperRow_51,
    starHelperRow_52,
    starHelperRow_53,
    starHelperRow_54,
    starHelperRow_55,
    starHelperRow_56,
    starHelperRow_57,
    starHelperRow_58,
    starHelperRow_59,
    starHelperRow_60,
    starHelperRow_61,
    starHelperRow_62,
    starHelperRow_63, Bool.false_or]

end PEqualNP.Outside.L_meta_2592
