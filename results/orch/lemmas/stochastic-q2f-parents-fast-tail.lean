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

