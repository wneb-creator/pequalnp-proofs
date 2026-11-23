import Mathlib
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def w : Nat := 22249865081872915941574148967880321589339528266059745471943816409629475331023819421187760106154
def total : Nat := ((List.range 3000).map fun i => (w / 2^(i % 302)) % 2).sum
example : total = 1769 := by decide +kernel
