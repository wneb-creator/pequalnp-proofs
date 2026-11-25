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

end PEqualNP.Outside.L_meta_2592
