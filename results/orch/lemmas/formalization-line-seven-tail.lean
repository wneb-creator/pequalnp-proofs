def line7_missing : Finset (Fin 7) := cap7_decode 49

def line7_superCode (k : Fin 15) : Fin 128 :=
  ![51,53,55,57,59,61,63,113,115,117,119,121,123,125,127] k

lemma line7_super_complete : ∀ m : Fin 128, line7_missing ⊂ cap7_decode m →
    ∃ k : Fin 15, line7_superCode k = m := by decide +kernel

lemma line7_super_card : ∀ k : Fin 15,
    4 ≤ (cap7_decode (line7_superCode k)).card := by decide +kernel

def line7_codes (s : Fin 15) (a b c : Fin 10) : Finset (Fin 128) :=
  {11,69,98,line7_superCode s,cap7_parentCode 0 a 0,cap7_parentCode 0 a 1,
    cap7_parentCode 1 b 0,cap7_parentCode 1 b 1,cap7_parentCode 2 c 0,cap7_parentCode 2 c 1}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_0 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 0 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_1 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 1 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_2 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 2 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_3 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 3 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_4 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 4 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_5 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 5 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_6 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 6 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_7 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 7 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_8 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 8 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_9 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 9 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_10 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 10 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_11 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 11 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_12 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 12 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_13 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 13 a b c).card := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line7_codes_card_14 : ∀ a b c : Fin 10, 7 ≤ (line7_codes 14 a b c).card := by
  decide +kernel

lemma line7_codes_card (s : Fin 15) (a b c : Fin 10) : 7 ≤ (line7_codes s a b c).card := by
  fin_cases s
  · exact line7_codes_card_0 a b c
  · exact line7_codes_card_1 a b c
  · exact line7_codes_card_2 a b c
  · exact line7_codes_card_3 a b c
  · exact line7_codes_card_4 a b c
  · exact line7_codes_card_5 a b c
  · exact line7_codes_card_6 a b c
  · exact line7_codes_card_7 a b c
  · exact line7_codes_card_8 a b c
  · exact line7_codes_card_9 a b c
  · exact line7_codes_card_10 a b c
  · exact line7_codes_card_11 a b c
  · exact line7_codes_card_12 a b c
  · exact line7_codes_card_13 a b c
  · exact line7_codes_card_14 a b c


lemma line7_seven_occurring_of_card
    (count : ∀ s : Fin 15, ∀ a b c : Fin 10, 7 ≤ (line7_codes s a b c).card)
    (Q : Finset (Fin 7) → Prop) (base : ∀ i : Fin 3, Q (cap7_triple i))
    (parents : ∀ i : Fin 3, cap7_Parent Q (cap7_triple i))
    (S : Finset (Fin 7)) (strict : line7_missing ⊂ S) (hS : Q S) :
    ∃ Y : Finset (Finset (Fin 7)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, Q M ∧ 2 ≤ M.card ∧ (M.card = 2 → ∃ i : Fin 3, M ⊆ cap7_triple i) := by
  obtain ⟨a,ha0,ha1⟩ := cap7_choose_parent Q 0 (parents 0)
  obtain ⟨b,hb0,hb1⟩ := cap7_choose_parent Q 1 (parents 1)
  obtain ⟨c,hc0,hc1⟩ := cap7_choose_parent Q 2 (parents 2)
  obtain ⟨s,hs⟩ := line7_super_complete (cap7_encode S) (by rw [cap7_decode_encode]; exact strict)
  have decodeS : cap7_decode (line7_superCode s) = S := by rw [hs,cap7_decode_encode]
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
  refine ⟨(line7_codes s a b c).image cap7_decode,?_,?_⟩
  · rw [Finset.card_image_of_injective _ cap7_decode_injective]
    exact count s a b c
  · intro M hM
    obtain ⟨m,hm,rfl⟩ := Finset.mem_image.mp hM
    simp only [line7_codes,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact basic 0
    · exact basic 1
    · exact basic 2
    · rw [decodeS]
      have hcard : 4 ≤ S.card := by simpa only [decodeS] using line7_super_card s
      exact ⟨hS,large _ (by omega)⟩
    · exact parentGood 0 a 0 ha0
    · exact parentGood 0 a 1 ha1
    · exact parentGood 1 b 0 hb0
    · exact parentGood 1 b 1 hb1
    · exact parentGood 2 c 0 hc0
    · exact parentGood 2 c 1 hc1

theorem line7_seven_occurring
    (Q : Finset (Fin 7) → Prop) (base : ∀ i : Fin 3, Q (cap7_triple i))
    (parents : ∀ i : Fin 3, cap7_Parent Q (cap7_triple i))
    (S : Finset (Fin 7)) (strict : line7_missing ⊂ S) (hS : Q S) :
    ∃ Y : Finset (Finset (Fin 7)), 7 ≤ Y.card ∧
      ∀ M ∈ Y, Q M ∧ 2 ≤ M.card ∧ (M.card = 2 → ∃ i : Fin 3, M ⊆ cap7_triple i) :=
  line7_seven_occurring_of_card line7_codes_card Q base parents S strict hS

