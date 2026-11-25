namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_decode_mem (m : Fin 128) (i : Fin 7) :
    i ∈ cap7_decode m ↔ m.val.testBit i.val = true := by
  simp [cap7_decode,Nat.testBit_eq_decide_div_mod_eq]

lemma q2f_decode_union (a b : Fin 128) :
    cap7_decode (q2f_union a b) = cap7_decode a ∪ cap7_decode b := by
  ext i
  simp only [Finset.mem_union,q2f_decode_mem]
  change (((a.val ||| b.val) % 2^7).testBit i.val = true) ↔ _
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

lemma q2f_decode_inter (a b : Fin 128) :
    cap7_decode (q2f_inter a b) = cap7_decode a ∩ cap7_decode b := by
  ext i
  simp only [Finset.mem_inter,q2f_decode_mem]
  change (((a.val &&& b.val) % 2^7).testBit i.val = true) ↔ _
  rw [Nat.testBit_mod_two_pow]
  simp [i.isLt]

lemma q2f_decode_diff (a b : Fin 128) :
    cap7_decode (q2f_diff a b) = cap7_decode a \ cap7_decode b := by
  ext i
  simp only [Finset.mem_sdiff,q2f_decode_mem]
  change (((a.val ^^^ (a.val &&& b.val)) % 2^7).testBit i.val = true) ↔ _
  rw [Nat.testBit_mod_two_pow]
  simp only [i.isLt,decide_true,Bool.true_and,Nat.testBit_xor,Nat.testBit_and]
  cases a.val.testBit i.val <;> cases b.val.testBit i.val <;> decide

lemma q2f_sub_iff (a b : Fin 128) :
    q2f_sub a b = true ↔ cap7_decode a ⊆ cap7_decode b := by
  have bound : a.val &&& b.val < 128 := lt_of_le_of_lt Nat.and_le_left a.isLt
  have intermediate : q2f_sub a b = true ↔ q2f_inter a b = a := by
    simp only [q2f_sub,decide_eq_true_eq,Fin.ext_iff,q2f_inter,Nat.mod_eq_of_lt bound]
  rw [intermediate]
  constructor
  · intro h
    have decoded := congrArg cap7_decode h
    rw [q2f_decode_inter] at decoded
    exact Finset.inter_eq_left.mp decoded
  · intro h
    apply cap7_decode_injective
    rw [q2f_decode_inter,Finset.inter_eq_left.mpr h]

def q2f_bridge_smallCode (k : Fin 29) : Fin 128 :=
  ![0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,64,65,66,68,72,80,96] k

lemma q2f_bridge_small_complete : ∀ m : Fin 128, cap7_card m ≤ 2 →
    ∃ k : Fin 29, q2f_bridge_smallCode k = m := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2f_cut_cover : ∀ i j : Fin 29,
    3 ≤ cap7_card (q2f_union (q2f_bridge_smallCode i) (q2f_bridge_smallCode j)) →
    let m := q2f_union (q2f_bridge_smallCode i) (q2f_bridge_smallCode j)
    (cap7_card m = 3 ∨ cap7_card m = 4) ∧ ∃ k : Fin 3,
      (q2f_sub (q2f_cut m k 0) (q2f_bridge_smallCode i) = true ∧
        q2f_sub (q2f_cut m k 1) (q2f_bridge_smallCode j) = true) ∨
      (q2f_sub (q2f_cut m k 0) (q2f_bridge_smallCode j) = true ∧
        q2f_sub (q2f_cut m k 1) (q2f_bridge_smallCode i) = true) := by
  decide +kernel

end PEqualNP.Outside.L_meta_6659_aux
