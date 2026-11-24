import Alt10495Prefix

namespace PEqualNP.Outside.L_meta_1677.O1677

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem benchmarkJ_first : auditBlock 9 0 2=true := by
  simp only [auditBlock,hybridBlock,Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [hybridNode,rankCount,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,rankNode,nodeSignedVerified,Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem benchmarkJ_rank : auditBlock 11 214 44=true := by
  simp only [auditBlock,hybridBlock,Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [hybridNode,rankCount,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,rankNode,nodeSignedVerified,Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem benchmarkJ_signed : auditBlock 12 797 44=true := by
  simp only [auditBlock,hybridBlock,Bool.and_eq_true]
  repeat' apply And.intro
  all_goals try simp only [hybridNode,rankCount,Nat.reduceAdd,Nat.reduceLT,ite_true,ite_false,rankNode,nodeSignedVerified,Bool.and_eq_true]
  all_goals repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_1677.O1677
