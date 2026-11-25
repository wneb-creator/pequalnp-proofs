import Init
theorem lowBit_shift_other (m i k:Nat) (h:k≠i):
 ((m &&& 1) <<< i).testBit k = false := by
 by_cases hi:i≤k
 · have hb:(1:Nat).testBit (k-i)=false := by
     apply Bool.eq_false_iff.mpr
     intro hbit
     have he:=Nat.testBit_one_eq_true_iff_self_eq_zero.mp hbit
     omega
   simp only [Nat.testBit_shiftLeft,Nat.testBit_and,hi,hb,decide_true,Bool.true_and,Bool.and_false]
 · simp [Nat.testBit_shiftLeft,hi]
theorem corner_other (raw m i j k:Nat) (hi:k≠i) (hj:k≠j):
 (raw ||| ((m &&& 1) <<< i) ||| (((m >>> 1) &&& 1) <<< j)).testBit k = raw.testBit k := by
 simp only [Nat.testBit_or,lowBit_shift_other m i k hi,
   lowBit_shift_other (m>>>1) j k hj,Bool.or_false]
