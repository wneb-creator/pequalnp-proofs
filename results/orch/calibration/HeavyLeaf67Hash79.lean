import ComputationalBounds
import DeepContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

def qBenchmarkHeavy : List (ℕ × ℕ) := grpSix ++ tg0 ++ grp5

#eval IO.eprintln "BEFORE heavy leaf67 hash79 mod127"
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def benchmarkHeavyLeaf :
    chkDeepSel (fun _ _ _ r => Nat.beq ((r.foldl (fun h w => h * 17 + w.s) 0) % 127) 79)
      [] qBenchmarkHeavy 0 13 1 (2 ^ 67) 0 = false := by
  decide +kernel
#eval IO.eprintln "AFTER heavy leaf67 hash79 mod127"

end PEqualNP.Outside.L_meta_10760_aux
