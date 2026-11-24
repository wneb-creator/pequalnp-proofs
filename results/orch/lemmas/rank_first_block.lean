import Alt10495Prefix

namespace PEqualNP.Outside.L_meta_1677.O1677

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem benchmarkFirstBlock : auditBlock 9 0 2 = true := by
  simp only [auditBlock, hybridBlock, Bool.and_eq_true]
  repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_1677.O1677
