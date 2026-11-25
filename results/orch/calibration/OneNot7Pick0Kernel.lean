import ComputationalBounds
import ContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

def qBenchmark7 : List (ℕ × ℕ) := grpSix

#eval IO.eprintln "BEFORE selector0 Q7 Kernel"
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def benchmarkSelector0 : chkSel (notPick 0) [] qBenchmark7 0 13 1 0 1 = false := by
  decide +kernel
#eval IO.eprintln "AFTER selector0 Q7 Kernel"

end PEqualNP.Outside.L_meta_10760_aux
