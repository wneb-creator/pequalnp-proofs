import PNPQ2FFinite
set_option maxRecDepth 100000
set_option maxHeartbeats 200000
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

set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_or_true_iff {a b : Bool} : (a || b) = true ↔ a = true ∨ b = true := by
  cases a <;> cases b <;> decide

lemma q2f_and_true_iff {a b : Bool} : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

lemma q2f_mem_iff (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_mem s a b c m = true ↔ m ∈ q2f_codes s a b c := by
  simp only [q2f_mem,q2f_codes,Bool.or_eq_true,decide_eq_true_eq,
    Finset.mem_insert,Finset.mem_singleton,or_assoc]

lemma q2f_mem_exists (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_mem s a b c m = true) : ∃ i : Fin 10, m = q2f_raw s a b c i := by
  simp only [q2f_mem,Bool.or_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩
  · exact ⟨4,h⟩
  · exact ⟨5,h⟩
  · exact ⟨6,h⟩
  · exact ⟨7,h⟩
  · exact ⟨8,h⟩
  · exact ⟨9,h⟩

lemma q2f_outside_correct : ∀ m : Fin 128,
    q2f_outside m = true ↔ (cap7_decode m).card = 2 ∧
      ∀ i : Fin 3, ¬ cap7_decode m ⊆ cap7_decode (q2f_tripleCode i) := by
  have coded : ∀ m : Fin 128, q2f_outside m = true ↔ cap7_card m = 2 ∧
      ∀ i : Fin 3, q2f_sub m (q2f_tripleCode i) = false := by decide +kernel
  intro m
  rw [coded,cap7_card_correct]
  constructor
  · rintro ⟨card,sub⟩
    refine ⟨card,?_⟩
    intro i hi
    have yes := (q2f_sub_iff _ _).mpr hi
    have no := sub i
    simp only [yes,Bool.true_eq_false] at no
  · rintro ⟨card,sub⟩
    refine ⟨card,?_⟩
    intro i
    cases hi : q2f_sub m (q2f_tripleCode i)
    · rfl
    · exact False.elim (sub i ((q2f_sub_iff _ _).mp hi))

lemma q2f_small_card (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_small s a b c m = true) : cap7_card m ≤ 2 := by
  simp only [q2f_small,Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with h | ⟨h,_⟩ <;> omega

lemma q2f_small_of_one (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : cap7_card m ≤ 1) : q2f_small s a b c m = true := by
  simp only [q2f_small,h,decide_true,Bool.true_or]

lemma q2f_small_of_allowed (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_allowed s a b c m = true) (low : cap7_card m ≤ 2) :
    q2f_small s a b c m = true := by
  rcases q2f_or_true_iff.mp h with small | member
  · exact small
  · by_cases one : cap7_card m ≤ 1
    · exact q2f_small_of_one s a b c m one
    · have two : cap7_card m = 2 := by omega
      simp only [q2f_small,two,member,decide_true,Bool.or_true,Bool.and_true]

lemma q2f_small_downward (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hy : q2f_small s a b c y = true) (sub : cap7_decode x ⊆ cap7_decode y) :
    q2f_small s a b c x = true := by
  have upper := q2f_small_card s a b c y hy
  have lower : cap7_card x ≤ cap7_card y := by
    rw [cap7_card_correct,cap7_card_correct]
    exact Finset.card_le_card sub
  by_cases one : cap7_card x ≤ 1
  · exact q2f_small_of_one s a b c x one
  · have equal : cap7_decode x = cap7_decode y :=
      Finset.eq_of_subset_of_card_le sub (by rw [← cap7_card_correct,← cap7_card_correct]; omega)
    exact (cap7_decode_injective equal) ▸ hy

lemma q2f_small_union_seed (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hx : q2f_small s a b c x = true) (hy : q2f_small s a b c y = true)
    (large : 3 ≤ cap7_card (q2f_union x y)) : q2f_seed s a b c (q2f_union x y) = true := by
  obtain ⟨i,hi⟩ := q2f_bridge_small_complete x (q2f_small_card s a b c x hx)
  obtain ⟨j,hj⟩ := q2f_bridge_small_complete y (q2f_small_card s a b c y hy)
  have coverage := q2f_cut_cover i j (by simpa only [hi,hj] using large)
  simp only [hi,hj] at coverage
  obtain ⟨card,k,parts⟩ := coverage
  have both : q2f_small s a b c (q2f_cut (q2f_union x y) k 0) = true ∧
      q2f_small s a b c (q2f_cut (q2f_union x y) k 1) = true := by
    rcases parts with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact ⟨q2f_small_downward s a b c _ x hx ((q2f_sub_iff _ _).mp h0),
        q2f_small_downward s a b c _ y hy ((q2f_sub_iff _ _).mp h1)⟩
    · exact ⟨q2f_small_downward s a b c _ y hy ((q2f_sub_iff _ _).mp h0),
        q2f_small_downward s a b c _ x hx ((q2f_sub_iff _ _).mp h1)⟩
  simp only [q2f_seed,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq]
  refine ⟨card,?_⟩
  fin_cases k
  · exact Or.inl (Or.inl both)
  · exact Or.inl (Or.inr both)
  · exact Or.inr both

lemma q2f_grow_union (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hy : q2f_small s a b c y = true) : q2f_grow s a b c x (q2f_union x y) = true := by
  apply q2f_and_true_iff.mpr
  constructor
  · apply (q2f_sub_iff _ _).mpr
    rw [q2f_decode_union]
    exact Finset.subset_union_left
  · apply q2f_small_downward s a b c _ y hy
    rw [q2f_decode_diff,q2f_decode_union]
    intro i hi
    simp only [Finset.mem_sdiff,Finset.mem_union] at hi
    tauto

lemma q2f_closed_of_small (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_small s a b c m = true) : q2f_closed s a b c m = true := by
  simp only [q2f_closed,h,Bool.true_or]

lemma q2f_closed_known (s : Fin 15) (a b c : Fin 10) (j : Fin 3) :
    q2f_closed s a b c (q2f_known s a b c j) = true := by
  simp only [q2f_closed,Bool.or_eq_true,decide_eq_true_eq]
  fin_cases j <;> tauto

lemma q2f_closed_cases (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_closed s a b c m = true) :
    q2f_small s a b c m = true ∨ ∃ j : Fin 3, m = q2f_known s a b c j := by
  simp only [q2f_closed,Bool.or_eq_true,decide_eq_true_eq,or_assoc] at h
  rcases h with small | h | h | h
  · exact Or.inl small
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩

lemma q2f_generators_node (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (i : Fin 10) : q2f_node s a b c i = true := by
  simp only [q2f_generators,Bool.and_eq_true,and_assoc] at h
  rcases h with ⟨n0,n1,n2,n3,n4,n5,n6,n7,n8,n9,_,_,_⟩
  fin_cases i
  · exact n0
  · exact n1
  · exact n2
  · exact n3
  · exact n4
  · exact n5
  · exact n6
  · exact n7
  · exact n8
  · exact n9

lemma q2f_closed_seed (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (m : Fin 128)
    (allowed : q2f_allowed s a b c m = true) (seed : q2f_seed s a b c m = true) :
    q2f_closed s a b c m = true := by
  rcases q2f_or_true_iff.mp allowed with small | member
  · exact q2f_closed_of_small s a b c m small
  · obtain ⟨i,hi⟩ := q2f_mem_exists s a b c m member
    have node := q2f_generators_node s a b c h i
    simpa only [q2f_node,← hi,seed,Bool.not_true,Bool.false_and,Bool.or_false] using node

lemma q2f_closed_grow (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (m : Fin 128)
    (allowed : q2f_allowed s a b c m = true) (j : Fin 3)
    (grow : q2f_grow s a b c (q2f_known s a b c j) m = true) :
    q2f_closed s a b c m = true := by
  rcases q2f_or_true_iff.mp allowed with small | member
  · exact q2f_closed_of_small s a b c m small
  · obtain ⟨i,hi⟩ := q2f_mem_exists s a b c m member
    have node := q2f_generators_node s a b c h i
    simp only [q2f_node,← hi,Bool.or_eq_true,Bool.and_eq_true] at node
    rcases node with closed | ⟨⟨⟨_,g0⟩,g1⟩,g2⟩
    · exact closed
    · fin_cases j
      · change q2f_grow s a b c (q2f_known s a b c 0) m = true at grow
        simp only [grow,Bool.not_true,Bool.false_eq_true] at g0
      · change q2f_grow s a b c (q2f_known s a b c 1) m = true at grow
        simp only [grow,Bool.not_true,Bool.false_eq_true] at g1
      · change q2f_grow s a b c (q2f_known s a b c 2) m = true at grow
        simp only [grow,Bool.not_true,Bool.false_eq_true] at g2

end PEqualNP.Outside.L_meta_6659_aux

set_option maxRecDepth 100000
set_option maxHeartbeats 200000
namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_union_comm (x y : Fin 128) : q2f_union x y = q2f_union y x := by
  apply cap7_decode_injective
  simp only [q2f_decode_union, Finset.union_comm]

lemma q2f_inter_comm (x y : Fin 128) : q2f_inter x y = q2f_inter y x := by
  apply cap7_decode_injective
  simp only [q2f_decode_inter, Finset.inter_comm]

lemma q2f_union_self (x : Fin 128) : q2f_union x x = x := by
  apply cap7_decode_injective
  simp only [q2f_decode_union, Finset.union_self]

lemma q2f_inter_self (x : Fin 128) : q2f_inter x x = x := by
  apply cap7_decode_injective
  simp only [q2f_decode_inter, Finset.inter_self]

lemma q2f_pair_comm (s : Fin 15) (a b c : Fin 10) (i j : Fin 3) :
    q2f_pair s a b c i j = q2f_pair s a b c j i := by
  simp only [q2f_pair, q2f_union_comm (q2f_known s a b c i),
    q2f_inter_comm (q2f_known s a b c i)]

lemma q2f_pair_self (s : Fin 15) (a b c : Fin 10) (i : Fin 3) :
    q2f_pair s a b c i i = true := by
  simp only [q2f_pair, q2f_union_self, q2f_inter_self,
    q2f_closed_known, Bool.or_true, Bool.true_and]

lemma q2f_generators_pair (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (i j : Fin 3) :
    q2f_pair s a b c i j = true := by
  have pairs : q2f_pair s a b c 0 1 = true ∧ q2f_pair s a b c 0 2 = true ∧
      q2f_pair s a b c 1 2 = true := by
    simp only [q2f_generators, Bool.and_eq_true, and_assoc] at h
    exact h.2.2.2.2.2.2.2.2.2.2
  fin_cases i <;> fin_cases j
  · exact q2f_pair_self s a b c 0
  · exact pairs.1
  · exact pairs.2.1
  · exact (q2f_pair_comm s a b c 1 0).trans pairs.1
  · exact q2f_pair_self s a b c 1
  · exact pairs.2.2
  · exact (q2f_pair_comm s a b c 2 0).trans pairs.2.1
  · exact (q2f_pair_comm s a b c 2 1).trans pairs.2.2
  · exact q2f_pair_self s a b c 2

lemma q2f_generators_union (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (x y : Fin 128)
    (hx : q2f_closed s a b c x = true) (hy : q2f_closed s a b c y = true)
    (allowed : q2f_allowed s a b c (q2f_union x y) = true) :
    q2f_closed s a b c (q2f_union x y) = true := by
  rcases q2f_closed_cases s a b c x hx with sx | ⟨i, rfl⟩
  · rcases q2f_closed_cases s a b c y hy with sy | ⟨j, rfl⟩
    · by_cases low : cap7_card (q2f_union x y) ≤ 2
      · exact q2f_closed_of_small s a b c _ (q2f_small_of_allowed s a b c _ allowed low)
      · exact q2f_closed_seed s a b c h _ allowed
          (q2f_small_union_seed s a b c x y sx sy (by omega))
    · rw [q2f_union_comm] at allowed ⊢
      exact q2f_closed_grow s a b c h _ allowed j (q2f_grow_union s a b c _ x sx)
  · rcases q2f_closed_cases s a b c y hy with sy | ⟨j, rfl⟩
    · exact q2f_closed_grow s a b c h _ allowed i (q2f_grow_union s a b c _ y sy)
    · have pair := q2f_generators_pair s a b c h i j
      have left := (q2f_and_true_iff.mp pair).1
      simpa only [allowed, Bool.not_true, Bool.false_or] using left

lemma q2f_generators_inter (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (x y : Fin 128)
    (hx : q2f_closed s a b c x = true) (hy : q2f_closed s a b c y = true)
    (allowed : q2f_allowed s a b c (q2f_inter x y) = true) :
    q2f_closed s a b c (q2f_inter x y) = true := by
  have fromSmall (u v : Fin 128) (small : q2f_small s a b c u = true)
      (ha : q2f_allowed s a b c (q2f_inter u v) = true) :
      q2f_closed s a b c (q2f_inter u v) = true := by
    apply q2f_closed_of_small s a b c _
    apply q2f_small_of_allowed s a b c _ ha
    calc
      cap7_card (q2f_inter u v) = (cap7_decode u ∩ cap7_decode v).card := by
        rw [cap7_card_correct, q2f_decode_inter]
      _ ≤ (cap7_decode u).card := Finset.card_le_card Finset.inter_subset_left
      _ ≤ 2 := by simpa only [cap7_card_correct] using q2f_small_card s a b c u small
  rcases q2f_closed_cases s a b c x hx with sx | ⟨i, rfl⟩
  · exact fromSmall x y sx allowed
  · rcases q2f_closed_cases s a b c y hy with sy | ⟨j, rfl⟩
    · rw [q2f_inter_comm] at allowed ⊢
      exact fromSmall y _ sy allowed
    · have pair := q2f_generators_pair s a b c h i j
      have right := (q2f_and_true_iff.mp pair).2
      simpa only [allowed, Bool.not_true, Bool.false_or] using right

lemma q2f_encode_union (A B : Finset (Fin 7)) :
    q2f_union (cap7_encode A) (cap7_encode B) = cap7_encode (A ∪ B) := by
  apply cap7_decode_injective
  simp only [q2f_decode_union, cap7_decode_encode]

lemma q2f_encode_inter (A B : Finset (Fin 7)) :
    q2f_inter (cap7_encode A) (cap7_encode B) = cap7_encode (A ∩ B) := by
  apply cap7_decode_injective
  simp only [q2f_decode_inter, cap7_decode_encode]

lemma q2f_closed_empty (s : Fin 15) (a b c : Fin 10) :
    q2f_closed s a b c (cap7_encode ∅) = true := by
  apply q2f_closed_of_small s a b c _
  apply q2f_small_of_one s a b c _
  simp only [cap7_card_correct, cap7_decode_encode, Finset.card_empty]
  omega

lemma q2f_closed_singleton (s : Fin 15) (a b c : Fin 10) (i : Fin 7) :
    q2f_closed s a b c (cap7_encode {i}) = true := by
  apply q2f_closed_of_small s a b c _
  apply q2f_small_of_one s a b c _
  simp only [cap7_card_correct, cap7_decode_encode, Finset.card_singleton, le_refl]

lemma q2f_finset_union (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (A B : Finset (Fin 7))
    (ha : q2f_closed s a b c (cap7_encode A) = true)
    (hb : q2f_closed s a b c (cap7_encode B) = true)
    (allowed : q2f_allowed s a b c (cap7_encode (A ∪ B)) = true) :
    q2f_closed s a b c (cap7_encode (A ∪ B)) = true := by
  rw [← q2f_encode_union] at allowed ⊢
  exact q2f_generators_union s a b c h _ _ ha hb allowed

lemma q2f_finset_inter (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (A B : Finset (Fin 7))
    (ha : q2f_closed s a b c (cap7_encode A) = true)
    (hb : q2f_closed s a b c (cap7_encode B) = true)
    (allowed : q2f_allowed s a b c (cap7_encode (A ∩ B)) = true) :
    q2f_closed s a b c (cap7_encode (A ∩ B)) = true := by
  rw [← q2f_encode_inter] at allowed ⊢
  exact q2f_generators_inter s a b c h _ _ ha hb allowed

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_raw_mem (s : Fin 15) (a b c : Fin 10) (i : Fin 10) :
    q2f_raw s a b c i ∈ q2f_codes s a b c := by
  apply (q2f_mem_iff s a b c _).mp
  simp only [q2f_mem, Bool.or_eq_true, decide_eq_true_eq]
  fin_cases i <;> tauto

lemma q2f_missing_mem (s : Fin 15) (a b c : Fin 10) :
    q2f_missing s a b c ∈ q2f_codes s a b c :=
  q2f_raw_mem s a b c _

lemma q2f_certificate_card (s : Fin 15) (a b c : Fin 10)
    (h : q2f_certificate s a b c = true) : 7 ≤ (q2f_codes s a b c).card := by
  exact of_decide_eq_true (q2f_and_true_iff.mp h).1

lemma q2f_certificate_shape (s : Fin 15) (a b c : Fin 10)
    (h : q2f_certificate s a b c = true)
    (bound : (q2f_codes s a b c).card ≤ 7)
    (closed : q2f_generators s a b c = true →
      ∀ m ∈ q2f_codes s a b c, q2f_closed s a b c m = true) :
    q2f_shape s a b c = true := by
  have alternatives := (q2f_and_true_iff.mp h).2
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, or_assoc] at alternatives
  rcases alternatives with eight | shape | ⟨generators,missing⟩
  · omega
  · exact shape
  · have yes := closed generators _ (q2f_missing_mem s a b c)
    simp only [yes, Bool.not_true, Bool.false_eq_true] at missing

lemma q2f_shape_member (s : Fin 15) (a b c : Fin 10)
    (h : q2f_shape s a b c = true) (m : Fin 128) (hm : m ∈ q2f_codes s a b c) :
    cap7_card m ≤ 2 ∨ m = 11 ∨ m = 69 ∨ m = 49 ∨ m = q2f_superCode s := by
  obtain ⟨i,rfl⟩ := q2f_mem_exists s a b c m ((q2f_mem_iff s a b c m).mpr hm)
  simp only [q2f_shape, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    and_assoc,or_assoc] at h
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9

lemma q2f_allowed_shape (s : Fin 15) (a b c : Fin 10)
    (h : q2f_shape s a b c = true) (m : Fin 128)
    (ha : q2f_allowed s a b c m = true) :
    cap7_card m ≤ 2 ∨ m = 11 ∨ m = 69 ∨ m = 49 ∨ m = q2f_superCode s := by
  rcases q2f_or_true_iff.mp ha with small | member
  · exact Or.inl (q2f_small_card s a b c m small)
  · exact q2f_shape_member s a b c h m ((q2f_mem_iff s a b c m).mp member)

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux
def q2f_triple (i : Fin 3) : Finset (Fin 7) := cap7_decode (q2f_tripleCode i)

def q2f_missingTriple : Finset (Fin 7) := cap7_decode 98

def q2f_fiveCode (k : Fin 21) : Fin 128 :=
  ![31,47,55,59,61,62,79,87,91,93,94,103,107,109,110,115,117,118,121,122,124] k

lemma q2f_five_complete : ∀ m : Fin 128, cap7_card m = 5 → ∃ k : Fin 21, q2f_fiveCode k = m := by
  decide +kernel

lemma q2f_pair_code_complete : ∀ i : Fin 3, ∀ m : Fin 128,
    cap7_card m = 2 → q2f_sub m (q2f_tripleCode i) = true →
      ∃ k : Fin 10, q2f_parentCode i k 0 = m ∧ q2f_parentCode i k 1 = m := by
  decide +kernel

lemma q2f_pair_complete (i : Fin 3) (m : Fin 128)
    (hc : cap7_card m = 2) (hs : cap7_decode m ⊆ q2f_triple i) :
    ∃ k : Fin 10, q2f_parentCode i k 0 = m ∧ q2f_parentCode i k 1 = m :=
  q2f_pair_code_complete i m hc ((q2f_sub_iff _ _).mpr hs)

lemma q2f_four_code_complete : ∀ i : Fin 3, ∀ m : Fin 128,
    cap7_card m = 4 → q2f_sub (q2f_tripleCode i) m = true →
      ∃ k : Fin 10, q2f_parentCode i k 0 = m ∧ q2f_parentCode i k 1 = m := by
  decide +kernel

lemma q2f_four_complete (i : Fin 3) (m : Fin 128)
    (hc : cap7_card m = 4) (hs : q2f_triple i ⊆ cap7_decode m) :
    ∃ k : Fin 10, q2f_parentCode i k 0 = m ∧ q2f_parentCode i k 1 = m :=
  q2f_four_code_complete i m hc ((q2f_sub_iff _ _).mpr hs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2f_five_pair_code_complete : ∀ i : Fin 3, ∀ a b : Fin 21,
    q2f_inter (q2f_fiveCode a) (q2f_fiveCode b) = q2f_tripleCode i →
      ∃ k : Fin 10,
        (q2f_parentCode i k 0 = q2f_fiveCode a ∧ q2f_parentCode i k 1 = q2f_fiveCode b) ∨
        (q2f_parentCode i k 0 = q2f_fiveCode b ∧ q2f_parentCode i k 1 = q2f_fiveCode a) := by
  decide +kernel

lemma q2f_five_pair_complete (i : Fin 3) (a b : Fin 21)
    (h : cap7_decode (q2f_fiveCode a) ∩ cap7_decode (q2f_fiveCode b) = q2f_triple i) :
    ∃ k : Fin 10,
      (q2f_parentCode i k 0 = q2f_fiveCode a ∧ q2f_parentCode i k 1 = q2f_fiveCode b) ∨
      (q2f_parentCode i k 0 = q2f_fiveCode b ∧ q2f_parentCode i k 1 = q2f_fiveCode a) := by
  apply q2f_five_pair_code_complete i a b
  apply cap7_decode_injective
  rw [q2f_decode_inter]
  exact h

lemma q2f_super_code_complete : ∀ m : Fin 128,
    q2f_sub 98 m = true → m ≠ 98 → ∃ k : Fin 15, q2f_superCode k = m := by
  decide +kernel

lemma q2f_super_complete (m : Fin 128) (h : q2f_missingTriple ⊂ cap7_decode m) :
    ∃ k : Fin 15, q2f_superCode k = m := by
  obtain ⟨sub,ne⟩ := Finset.ssubset_iff_subset_ne.mp h
  apply q2f_super_code_complete m ((q2f_sub_iff _ _).mpr sub)
  intro eq
  apply ne
  rw [eq]
  rfl

lemma q2f_parent_code_good : ∀ i : Fin 3, ∀ k : Fin 10, ∀ side : Fin 2,
    2 ≤ cap7_card (q2f_parentCode i k side) ∧
      (cap7_card (q2f_parentCode i k side) = 2 →
        q2f_sub (q2f_parentCode i k side) (q2f_tripleCode i) = true) := by
  decide +kernel

lemma q2f_parent_good (i : Fin 3) (k : Fin 10) (side : Fin 2) :
    2 ≤ (cap7_decode (q2f_parentCode i k side)).card ∧
      ((cap7_decode (q2f_parentCode i k side)).card = 2 →
        cap7_decode (q2f_parentCode i k side) ⊆ q2f_triple i) := by
  obtain ⟨hc,hs⟩ := q2f_parent_code_good i k side
  refine ⟨by simpa only [cap7_card_correct] using hc,?_⟩
  intro two
  exact (q2f_sub_iff _ _).mp (hs (by simpa only [cap7_card_correct] using two))

lemma q2f_triple_card (i : Fin 3) : (q2f_triple i).card = 3 := by
  change (cap7_decode (q2f_tripleCode i)).card = 3
  rw [← cap7_card_correct]
  fin_cases i <;> rfl

lemma q2f_super_card : ∀ k : Fin 15, 4 ≤ (cap7_decode (q2f_superCode k)).card := by
  intro k
  rw [← cap7_card_correct]
  fin_cases k <;> decide

def q2f_Parent (Q : Finset (Fin 7) → Prop) (T : Finset (Fin 7)) : Prop :=
  (∃ A, Q A ∧ A.card = 2 ∧ A ⊆ T) ∨
    (∃ A, Q A ∧ A.card = 4 ∧ T ⊆ A) ∨
    (∃ A B, A ≠ B ∧ Q A ∧ Q B ∧ A.card = 5 ∧ B.card = 5 ∧
      T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T)

lemma q2f_choose_parent (Q : Finset (Fin 7) → Prop) (i : Fin 3)
    (h : q2f_Parent Q (q2f_triple i)) :
    ∃ k : Fin 10, Q (cap7_decode (q2f_parentCode i k 0)) ∧
      Q (cap7_decode (q2f_parentCode i k 1)) := by
  rcases h with ⟨A,hA,card,sub⟩ | ⟨A,hA,card,sub⟩ | ⟨A,B,_,hA,hB,ca,cb,_,_,inter⟩
  · have hc : cap7_card (cap7_encode A) = 2 := by rw [cap7_card_correct,cap7_decode_encode]; exact card
    have hs : cap7_decode (cap7_encode A) ⊆ q2f_triple i := by rw [cap7_decode_encode]; exact sub
    obtain ⟨k,ha,hb⟩ := q2f_pair_complete i (cap7_encode A) hc hs
    refine ⟨k,?_,?_⟩ <;> simpa only [ha,hb,cap7_decode_encode] using hA
  · have hc : cap7_card (cap7_encode A) = 4 := by rw [cap7_card_correct,cap7_decode_encode]; exact card
    have hs : q2f_triple i ⊆ cap7_decode (cap7_encode A) := by rw [cap7_decode_encode]; exact sub
    obtain ⟨k,ha,hb⟩ := q2f_four_complete i (cap7_encode A) hc hs
    refine ⟨k,?_,?_⟩ <;> simpa only [ha,hb,cap7_decode_encode] using hA
  · have hca : cap7_card (cap7_encode A) = 5 := by rw [cap7_card_correct,cap7_decode_encode]; exact ca
    have hcb : cap7_card (cap7_encode B) = 5 := by rw [cap7_card_correct,cap7_decode_encode]; exact cb
    obtain ⟨a,ha⟩ := q2f_five_complete (cap7_encode A) hca
    obtain ⟨b,hb⟩ := q2f_five_complete (cap7_encode B) hcb
    have hqa : Q (cap7_decode (q2f_fiveCode a)) := by simpa only [ha,cap7_decode_encode] using hA
    have hqb : Q (cap7_decode (q2f_fiveCode b)) := by simpa only [hb,cap7_decode_encode] using hB
    have hi : cap7_decode (q2f_fiveCode a) ∩ cap7_decode (q2f_fiveCode b) = q2f_triple i := by
      simpa only [ha,hb,cap7_decode_encode] using inter
    obtain ⟨k,hk⟩ := q2f_five_pair_complete i a b hi
    refine ⟨k,?_⟩
    rcases hk with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact ⟨by simpa only [h0] using hqa,by simpa only [h1] using hqb⟩
    · exact ⟨by simpa only [h0] using hqb,by simpa only [h1] using hqa⟩


lemma q2f_choose_family
    (Q : Finset (Fin 7) → Prop) (base : ∀ i : Fin 3, Q (q2f_triple i))
    (parents : ∀ i : Fin 3, q2f_Parent Q (q2f_triple i))
    (S : Finset (Fin 7)) (strict : q2f_missingTriple ⊂ S) (hS : Q S) :
    ∃ s : Fin 15, ∃ a b c : Fin 10, cap7_decode (q2f_superCode s) = S ∧
      ∀ m ∈ q2f_codes s a b c, Q (cap7_decode m) ∧ 2 ≤ (cap7_decode m).card ∧
        ((cap7_decode m).card = 2 → ∃ i : Fin 3, cap7_decode m ⊆ q2f_triple i) := by
  obtain ⟨a,ha0,ha1⟩ := q2f_choose_parent Q 0 (parents 0)
  obtain ⟨b,hb0,hb1⟩ := q2f_choose_parent Q 1 (parents 1)
  obtain ⟨c,hc0,hc1⟩ := q2f_choose_parent Q 2 (parents 2)
  obtain ⟨s,hs⟩ := q2f_super_complete (cap7_encode S) (by rw [cap7_decode_encode]; exact strict)
  have decodeS : cap7_decode (q2f_superCode s) = S := by rw [hs,cap7_decode_encode]
  have large (M : Finset (Fin 7)) (hm : 3 ≤ M.card) :
      2 ≤ M.card ∧ (M.card = 2 → ∃ i : Fin 3, M ⊆ q2f_triple i) := by
    constructor
    · omega
    · intro he
      omega
  have basic (i : Fin 3) : Q (q2f_triple i) ∧ 2 ≤ (q2f_triple i).card ∧
      ((q2f_triple i).card = 2 → ∃ j : Fin 3, q2f_triple i ⊆ q2f_triple j) :=
    ⟨base i,large _ (by rw [q2f_triple_card])⟩
  have parentGood (i : Fin 3) (k : Fin 10) (side : Fin 2)
      (hq : Q (cap7_decode (q2f_parentCode i k side))) :
      Q (cap7_decode (q2f_parentCode i k side)) ∧
        2 ≤ (cap7_decode (q2f_parentCode i k side)).card ∧
        ((cap7_decode (q2f_parentCode i k side)).card = 2 →
          ∃ j : Fin 3, cap7_decode (q2f_parentCode i k side) ⊆ q2f_triple j) :=
    ⟨hq,(q2f_parent_good i k side).1,fun h => ⟨i,(q2f_parent_good i k side).2 h⟩⟩
  refine ⟨s,a,b,c,decodeS,?_⟩
  intro m hm
  simp only [q2f_codes,Finset.mem_insert,Finset.mem_singleton] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact basic 0
  · exact basic 1
  · exact basic 2
  · change Q (cap7_decode (q2f_superCode s)) ∧
      2 ≤ (cap7_decode (q2f_superCode s)).card ∧
      ((cap7_decode (q2f_superCode s)).card = 2 →
        ∃ i : Fin 3, cap7_decode (q2f_superCode s) ⊆ q2f_triple i)
    rw [decodeS]
    have hcard : 4 ≤ S.card := by simpa only [decodeS] using q2f_super_card s
    exact ⟨hS,large _ (by omega)⟩
  · exact parentGood 0 a 0 ha0
  · exact parentGood 0 a 1 ha1
  · exact parentGood 1 b 0 hb0
  · exact parentGood 1 b 1 hb1
  · exact parentGood 2 c 0 hc0
  · exact parentGood 2 c 1 hc1


end PEqualNP.Outside.L_meta_6659_aux
