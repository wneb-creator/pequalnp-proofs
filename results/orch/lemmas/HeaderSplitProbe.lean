import FastBench

namespace PEqualNP.Outside.L_meta_1677_HeaderSplitProbe
open PEqualNP.Outside.L_meta_1677 PEqualNP.Outside.L_meta_1677_FastBench

def combined (k offset ar : Nat) : Bool :=
  let cs := seedContexts k offset 16
  cs.all (fun c => c.2.1==ar && prelim graph c) && probe_runBatch true k ar cs

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem split_11 : combined 11 1003 11 = true := by
  simp only [combined, Bool.and_eq_true]
  constructor <;> decide +kernel

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem split_12 : combined 12 901 12 = true := by
  simp only [combined, Bool.and_eq_true]
  constructor <;> decide +kernel

end PEqualNP.Outside.L_meta_1677_HeaderSplitProbe
