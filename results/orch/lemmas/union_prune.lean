import Mathlib.Data.Nat.Bitwise

namespace PEqualNP.Outside.L_meta_2592

def starMasks : List ℕ := [22, 37, 25, 42]

def singletonMasks : List ℕ := [1, 2, 4, 8, 16, 32]

def helperMasks : List ℕ :=
  (List.range 64).filter fun x =>
    x != 0 && Nat.land x (x - 1) != 0 && !(starMasks.contains x)

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

def starHelperSearch : Bool :=
  helperMasks.any fun a => helperMasks.any fun b =>
    if a < b then helperMasks.any fun c =>
      if b < c then starTripleSucceeds a b c else false
    else false

set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma starHelperSearch_false : starHelperSearch = false := by
  decide

end PEqualNP.Outside.L_meta_2592
