import ComputationalBounds
import ContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

def qBenchmark35 : List (ℕ × ℕ) := grpSix ++ tg0 ++ grp5

#eval IO.eprintln "BEFORE selector6 Kernel"
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def benchmarkSelector6 : chkSel (notPick 6) [] qBenchmark35 0 13 1 0 1 = false := by
  decide +kernel
#eval IO.eprintln "AFTER selector6 Kernel"

end PEqualNP.Outside.L_meta_10760_aux
