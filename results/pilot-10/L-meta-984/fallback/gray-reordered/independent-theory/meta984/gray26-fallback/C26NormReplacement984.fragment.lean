-- Replace existing C26_ori and C26_ori_run; do not append duplicate declarations.
def C26_ori : List Nat → List Nat := qGrayNormOrbit C26_grayWalk
theorem C26_ori_run {s : Nat} {ws : List Nat}
    (h : MonRun (compactGoal 9 9) s ws) :
    MonRun (compactGoal 9 9) s (C26_ori ws) := qGrayNormOrbit_run h C26_grayGood
