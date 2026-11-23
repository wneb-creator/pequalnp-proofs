-- Scratch fallback only. Not Lean-compiled; no full lower-bound claim.
def C26_grayRoute8 : List (Nat × Nat) := [(0x2aa,1)]
def C26_grayRoute2 : List (Nat × Nat) := [(0x800,1),(0x66,2)]
def C26_grayRoute1 : List (Nat × Nat) := [(0x2000,1),(0x1e,4)]
def C26_grayRoute16 : List (Nat × Nat) := [(0x8044,1),(0x600,2)]
def C26_grayRoute4 : List (Nat × Nat) := [(0x10000,1),(0x1818,2)]
def C26_grayWalk : List (List (Nat × Nat)) :=
  [C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute16,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute4,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute16,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute4,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute16,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8,C26_grayRoute1,C26_grayRoute8,C26_grayRoute2,C26_grayRoute8]
theorem C26_grayGood : qGrayGood (compactGoal 9 9) C26_grayWalk = true := by decide +kernel
def C26_grayOri : List Nat → List Nat := qGrayOrbit C26_grayWalk
theorem C26_grayOri_run {s : Nat} {ws : List Nat}
    (h : MonRun (compactGoal 9 9) s ws) :
    MonRun (compactGoal 9 9) s (C26_grayOri ws) := qGrayOrbit_run h C26_grayGood
def C26_grayNormOri : List Nat → List Nat := qGrayNormOrbit C26_grayWalk
theorem C26_grayNormOri_run {s : Nat} {ws : List Nat}
    (h : MonRun (compactGoal 9 9) s ws) :
    MonRun (compactGoal 9 9) s (C26_grayNormOri ws) := qGrayNormOrbit_run h C26_grayGood
