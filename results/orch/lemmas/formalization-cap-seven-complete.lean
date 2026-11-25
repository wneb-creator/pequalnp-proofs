import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6659_aux

def cap7_decode (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter (fun i => m.val / 2^i.val % 2 = 1)

def cap7_sum (S : Finset (Fin 7)) : ℕ := S.sum (fun i => 2^i.val)

lemma cap7_sum_bound : ∀ S : Finset (Fin 7), cap7_sum S < 128 := by decide +kernel

def cap7_encode (S : Finset (Fin 7)) : Fin 128 := ⟨cap7_sum S,cap7_sum_bound S⟩

lemma cap7_encode_decode : ∀ m : Fin 128, cap7_encode (cap7_decode m) = m := by decide +kernel
lemma cap7_decode_encode : ∀ S : Finset (Fin 7), cap7_decode (cap7_encode S) = S := by decide +kernel
lemma cap7_decode_injective : Function.Injective cap7_decode := by
  intro a b h
  have eq := congrArg cap7_encode h
  simpa only [cap7_encode_decode] using eq

def cap7_card (m : Fin 128) : ℕ :=
  ![0,1,1,2,1,2,2,3,1,2,2,3,2,3,3,4,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,1,2,2,3,2,3,3,4,2,3,3,4,3,4,4,5,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,2,3,3,4,3,4,4,5,3,4,4,5,4,5,5,6,3,4,4,5,4,5,5,6,4,5,5,6,5,6,6,7] m

lemma cap7_card_correct : ∀ m : Fin 128, cap7_card m = (cap7_decode m).card := by decide +kernel

def cap7_tripleCode (i : Fin 3) : Fin 128 := ![11,69,98] i

def cap7_triple (i : Fin 3) : Finset (Fin 7) := cap7_decode (cap7_tripleCode i)
def cap7_missing : Finset (Fin 7) := cap7_decode 44

def cap7_parentCode (i : Fin 3) (k : Fin 10) (side : Fin 2) : Fin 128 :=
  ![![![3,3],![9,9],![10,10],![15,15],![27,27],![43,43],![75,75],![31,107],![47,91],![59,79]],
    ![![5,5],![65,65],![68,68],![71,71],![77,77],![85,85],![101,101],![79,117],![87,109],![93,103]],
    ![![34,34],![66,66],![96,96],![99,99],![102,102],![106,106],![114,114],![103,122],![107,118],![110,115]]] i k side

def cap7_superCode (k : Fin 15) : Fin 128 :=
  ![45,46,47,60,61,62,63,108,109,110,111,124,125,126,127] k

def cap7_fiveCode (k : Fin 21) : Fin 128 :=
  ![31,47,55,59,61,62,79,87,91,93,94,103,107,109,110,115,117,118,121,122,124] k

lemma cap7_five_complete : ∀ m : Fin 128, cap7_card m = 5 → ∃ k : Fin 21, cap7_fiveCode k = m := by
  decide +kernel

lemma cap7_pair_complete : ∀ i : Fin 3, ∀ m : Fin 128,
    cap7_card m = 2 → cap7_decode m ⊆ cap7_triple i →
      ∃ k : Fin 10, cap7_parentCode i k 0 = m ∧ cap7_parentCode i k 1 = m := by
  decide +kernel

lemma cap7_four_complete : ∀ i : Fin 3, ∀ m : Fin 128,
    cap7_card m = 4 → cap7_triple i ⊆ cap7_decode m →
      ∃ k : Fin 10, cap7_parentCode i k 0 = m ∧ cap7_parentCode i k 1 = m := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_five_pair_complete : ∀ i : Fin 3, ∀ a b : Fin 21,
    cap7_decode (cap7_fiveCode a) ∩ cap7_decode (cap7_fiveCode b) = cap7_triple i →
      ∃ k : Fin 10,
        (cap7_parentCode i k 0 = cap7_fiveCode a ∧ cap7_parentCode i k 1 = cap7_fiveCode b) ∨
        (cap7_parentCode i k 0 = cap7_fiveCode b ∧ cap7_parentCode i k 1 = cap7_fiveCode a) := by
  decide +kernel

lemma cap7_super_complete : ∀ m : Fin 128, cap7_missing ⊂ cap7_decode m →
    ∃ k : Fin 15, cap7_superCode k = m := by decide +kernel

lemma cap7_parent_good : ∀ i : Fin 3, ∀ k : Fin 10, ∀ side : Fin 2,
    2 ≤ (cap7_decode (cap7_parentCode i k side)).card ∧
      ((cap7_decode (cap7_parentCode i k side)).card = 2 →
        cap7_decode (cap7_parentCode i k side) ⊆ cap7_triple i) := by decide +kernel

lemma cap7_triple_card : ∀ i : Fin 3, (cap7_triple i).card = 3 := by decide +kernel
lemma cap7_super_card : ∀ k : Fin 15, 4 ≤ (cap7_decode (cap7_superCode k)).card := by decide +kernel

def cap7_codes (s : Fin 15) (a b c : Fin 10) : Finset (Fin 128) :=
  {11,69,98,cap7_superCode s,cap7_parentCode 0 a 0,cap7_parentCode 0 a 1,
    cap7_parentCode 1 b 0,cap7_parentCode 1 b 1,cap7_parentCode 2 c 0,cap7_parentCode 2 c 1}


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_0 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 0 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_1 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 1 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_2 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 2 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_3 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 3 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_4 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 4 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_5 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 5 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_6 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 6 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_7 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 7 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_8 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 8 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_9 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 9 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_10 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 10 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_11 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 11 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_12 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 12 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_13 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 13 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma cap7_codes_card_14 : ∀ a b c : Fin 10, 7 ≤ (cap7_codes 14 a b c).card := by
  decide +kernel

lemma cap7_codes_card (s : Fin 15) (a b c : Fin 10) : 7 ≤ (cap7_codes s a b c).card := by
  fin_cases s
  · exact cap7_codes_card_0 a b c
  · exact cap7_codes_card_1 a b c
  · exact cap7_codes_card_2 a b c
  · exact cap7_codes_card_3 a b c
  · exact cap7_codes_card_4 a b c
  · exact cap7_codes_card_5 a b c
  · exact cap7_codes_card_6 a b c
  · exact cap7_codes_card_7 a b c
  · exact cap7_codes_card_8 a b c
  · exact cap7_codes_card_9 a b c
  · exact cap7_codes_card_10 a b c
  · exact cap7_codes_card_11 a b c
  · exact cap7_codes_card_12 a b c
  · exact cap7_codes_card_13 a b c
  · exact cap7_codes_card_14 a b c

def cap7_Parent (Q : Finset (Fin 7) → Prop) (T : Finset (Fin 7)) : Prop :=
  (∃ A, Q A ∧ A.card = 2 ∧ A ⊆ T) ∨
    (∃ A, Q A ∧ A.card = 4 ∧ T ⊆ A) ∨
    (∃ A B, A ≠ B ∧ Q A ∧ Q B ∧ A.card = 5 ∧ B.card = 5 ∧
      T ⊆ A ∧ T ⊆ B ∧ A ∩ B = T)

lemma cap7_choose_parent (Q : Finset (Fin 7) → Prop) (i : Fin 3)
    (h : cap7_Parent Q (cap7_triple i)) :
    ∃ k : Fin 10, Q (cap7_decode (cap7_parentCode i k 0)) ∧
      Q (cap7_decode (cap7_parentCode i k 1)) := by
  rcases h with ⟨A,hA,card,sub⟩ | ⟨A,hA,card,sub⟩ | ⟨A,B,_,hA,hB,ca,cb,_,_,inter⟩
  · have hc : cap7_card (cap7_encode A) = 2 := by rw [cap7_card_correct,cap7_decode_encode]; exact card
    have hs : cap7_decode (cap7_encode A) ⊆ cap7_triple i := by rw [cap7_decode_encode]; exact sub
    obtain ⟨k,ha,hb⟩ := cap7_pair_complete i (cap7_encode A) hc hs
    refine ⟨k,?_,?_⟩ <;> simpa only [ha,hb,cap7_decode_encode] using hA
  · have hc : cap7_card (cap7_encode A) = 4 := by rw [cap7_card_correct,cap7_decode_encode]; exact card
    have hs : cap7_triple i ⊆ cap7_decode (cap7_encode A) := by rw [cap7_decode_encode]; exact sub
    obtain ⟨k,ha,hb⟩ := cap7_four_complete i (cap7_encode A) hc hs
    refine ⟨k,?_,?_⟩ <;> simpa only [ha,hb,cap7_decode_encode] using hA
  · have hca : cap7_card (cap7_encode A) = 5 := by rw [cap7_card_correct,cap7_decode_encode]; exact ca
    have hcb : cap7_card (cap7_encode B) = 5 := by rw [cap7_card_correct,cap7_decode_encode]; exact cb
    obtain ⟨a,ha⟩ := cap7_five_complete (cap7_encode A) hca
    obtain ⟨b,hb⟩ := cap7_five_complete (cap7_encode B) hcb
    have hqa : Q (cap7_decode (cap7_fiveCode a)) := by simpa only [ha,cap7_decode_encode] using hA
    have hqb : Q (cap7_decode (cap7_fiveCode b)) := by simpa only [hb,cap7_decode_encode] using hB
    have hi : cap7_decode (cap7_fiveCode a) ∩ cap7_decode (cap7_fiveCode b) = cap7_triple i := by
      simpa only [ha,hb,cap7_decode_encode] using inter
    obtain ⟨k,hk⟩ := cap7_five_pair_complete i a b hi
    refine ⟨k,?_⟩
    rcases hk with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact ⟨by simpa only [h0] using hqa,by simpa only [h1] using hqb⟩
    · exact ⟨by simpa only [h0] using hqb,by simpa only [h1] using hqa⟩

lemma cap7_seven_occurring_of_card
    (count : ∀ s : Fin 15, ∀ a b c : Fin 10, 7 ≤ (cap7_codes s a b c).card)
    (Q : Finset (Fin 7) → Prop) (base : ∀ i : Fin 3, Q (cap7_triple i))
    (parents : ∀ i : Fin 3, cap7_Parent Q (cap7_triple i))
    (S : Finset (Fin 7)) (strict : cap7_missing ⊂ S) (hS : Q S) :
    ∃ Y : Finset (Finset (Fin 7)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, Q M ∧ 2 ≤ M.card ∧ (M.card = 2 → ∃ i : Fin 3, M ⊆ cap7_triple i) := by
  obtain ⟨a,ha0,ha1⟩ := cap7_choose_parent Q 0 (parents 0)
  obtain ⟨b,hb0,hb1⟩ := cap7_choose_parent Q 1 (parents 1)
  obtain ⟨c,hc0,hc1⟩ := cap7_choose_parent Q 2 (parents 2)
  obtain ⟨s,hs⟩ := cap7_super_complete (cap7_encode S) (by rw [cap7_decode_encode]; exact strict)
  have decodeS : cap7_decode (cap7_superCode s) = S := by rw [hs,cap7_decode_encode]
  have large (M : Finset (Fin 7)) (hm : 3 ≤ M.card) :
      2 ≤ M.card ∧ (M.card = 2 → ∃ i : Fin 3, M ⊆ cap7_triple i) := by
    constructor
    · omega
    · intro he
      omega
  have basic (i : Fin 3) : Q (cap7_triple i) ∧ 2 ≤ (cap7_triple i).card ∧
      ((cap7_triple i).card = 2 → ∃ j : Fin 3, cap7_triple i ⊆ cap7_triple j) :=
    ⟨base i,large _ (by rw [cap7_triple_card])⟩
  have parentGood (i : Fin 3) (k : Fin 10) (side : Fin 2)
      (hq : Q (cap7_decode (cap7_parentCode i k side))) :
      Q (cap7_decode (cap7_parentCode i k side)) ∧
        2 ≤ (cap7_decode (cap7_parentCode i k side)).card ∧
        ((cap7_decode (cap7_parentCode i k side)).card = 2 →
          ∃ j : Fin 3, cap7_decode (cap7_parentCode i k side) ⊆ cap7_triple j) :=
    ⟨hq,(cap7_parent_good i k side).1,fun h => ⟨i,(cap7_parent_good i k side).2 h⟩⟩
  refine ⟨(cap7_codes s a b c).image cap7_decode,?_,?_⟩
  · rw [Finset.card_image_of_injective _ cap7_decode_injective]
    exact count s a b c
  · intro M hM
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hM
    simp only [cap7_codes,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact basic 0
    · exact basic 1
    · exact basic 2
    · rw [decodeS]
      have hcard : 4 ≤ S.card := by simpa only [decodeS] using cap7_super_card s
      exact ⟨hS,large _ (by omega)⟩
    · exact parentGood 0 a 0 ha0
    · exact parentGood 0 a 1 ha1
    · exact parentGood 1 b 0 hb0
    · exact parentGood 1 b 1 hb1
    · exact parentGood 2 c 0 hc0
    · exact parentGood 2 c 1 hc1

theorem cap7_seven_occurring
    (Q : Finset (Fin 7) → Prop) (base : ∀ i : Fin 3, Q (cap7_triple i))
    (parents : ∀ i : Fin 3, cap7_Parent Q (cap7_triple i))
    (S : Finset (Fin 7)) (strict : cap7_missing ⊂ S) (hS : Q S) :
    ∃ Y : Finset (Finset (Fin 7)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, Q M ∧ 2 ≤ M.card ∧ (M.card = 2 → ∃ i : Fin 3, M ⊆ cap7_triple i) :=
  cap7_seven_occurring_of_card cap7_codes_card Q base parents S strict hS

end PEqualNP.Outside.L_meta_6659_aux
