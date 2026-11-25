import PNPQ2FBenchmark
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PEqualNP.Outside.L_meta_6659_aux

lemma q2f_mem_iff (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_mem s a b c m = true ↔ m ∈ q2f_codes s a b c := by
  simp only [q2f_mem,q2f_codes,Bool.or_eq_true,decide_eq_true_eq,
    Finset.mem_insert,Finset.mem_singleton] <;> tauto

lemma q2f_mem_exists (s : Fin 15) (a b c : Fin 10) (m : Fin 128)
    (h : q2f_mem s a b c m = true) : ∃ i : Fin 10, m = q2f_raw s a b c i := by
  simp only [q2f_mem,Bool.or_eq_true,decide_eq_true_eq] at h
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
  decide +kernel

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
  rcases Bool.or_eq_true.mp h with small | member
  · exact small
  · by_cases one : cap7_card m ≤ 1
    · exact q2f_small_of_one s a b c m one
    · have two : cap7_card m = 2 := by omega
      simp only [q2f_small,two,member,decide_true,Bool.or_true,Bool.and_true]
      decide

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
  simp only [q2f_seed,Bool.and_eq_true,decide_eq_true_eq]
  refine ⟨card,?_⟩
  fin_cases k <;> simp only [both.1,both.2,Bool.true_and,Bool.true_or,Bool.or_true]

lemma q2f_grow_union (s : Fin 15) (a b c : Fin 10) (x y : Fin 128)
    (hy : q2f_small s a b c y = true) : q2f_grow s a b c x (q2f_union x y) = true := by
  apply Bool.and_eq_true.mpr
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
  simp only [q2f_closed,Bool.or_eq_true,decide_eq_true_eq] at h
  rcases h with small | h | h | h
  · exact Or.inl small
  · exact Or.inr ⟨0,h⟩
  · exact Or.inr ⟨1,h⟩
  · exact Or.inr ⟨2,h⟩

lemma q2f_generators_node (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (i : Fin 10) : q2f_node s a b c i = true := by
  simp only [q2f_generators,Bool.and_eq_true] at h
  fin_cases i <;> tauto

lemma q2f_closed_seed (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (m : Fin 128)
    (allowed : q2f_allowed s a b c m = true) (seed : q2f_seed s a b c m = true) :
    q2f_closed s a b c m = true := by
  rcases Bool.or_eq_true.mp allowed with small | member
  · exact q2f_closed_of_small s a b c m small
  · obtain ⟨i,hi⟩ := q2f_mem_exists s a b c m member
    have node := q2f_generators_node s a b c h i
    simpa only [q2f_node,← hi,seed,Bool.not_true,Bool.false_and,Bool.or_false] using node

lemma q2f_closed_grow (s : Fin 15) (a b c : Fin 10)
    (h : q2f_generators s a b c = true) (m : Fin 128)
    (allowed : q2f_allowed s a b c m = true) (j : Fin 3)
    (grow : q2f_grow s a b c (q2f_known s a b c j) m = true) :
    q2f_closed s a b c m = true := by
  rcases Bool.or_eq_true.mp allowed with small | member
  · exact q2f_closed_of_small s a b c m small
  · obtain ⟨i,hi⟩ := q2f_mem_exists s a b c m member
    have node := q2f_generators_node s a b c h i
    fin_cases j <;>
      simpa only [q2f_node,← hi,grow,Bool.not_true,Bool.and_false,Bool.false_and,Bool.or_false] using node

end PEqualNP.Outside.L_meta_6659_aux

namespace PEqualNP.Outside.L_meta_6659_aux
def q2f_triple (i : Fin 3) : Finset (Fin 7) := cap7_decode (q2f_tripleCode i)

def q2f_missingTriple : Finset (Fin 7) := cap7_decode 98

def q2f_fiveCode (k : Fin 21) : Fin 128 :=
  ![31,47,55,59,61,62,79,87,91,93,94,103,107,109,110,115,117,118,121,122,124] k

lemma q2f_five_complete : ∀ m : Fin 128, cap7_card m = 5 → ∃ k : Fin 21, q2f_fiveCode k = m := by
  decide +kernel

lemma q2f_pair_complete : ∀ i : Fin 3, ∀ m : Fin 128,
    cap7_card m = 2 → cap7_decode m ⊆ q2f_triple i →
      ∃ k : Fin 10, q2f_parentCode i k 0 = m ∧ q2f_parentCode i k 1 = m := by
  decide +kernel

lemma q2f_four_complete : ∀ i : Fin 3, ∀ m : Fin 128,
    cap7_card m = 4 → q2f_triple i ⊆ cap7_decode m →
      ∃ k : Fin 10, q2f_parentCode i k 0 = m ∧ q2f_parentCode i k 1 = m := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2f_five_pair_complete : ∀ i : Fin 3, ∀ a b : Fin 21,
    cap7_decode (q2f_fiveCode a) ∩ cap7_decode (q2f_fiveCode b) = q2f_triple i →
      ∃ k : Fin 10,
        (q2f_parentCode i k 0 = q2f_fiveCode a ∧ q2f_parentCode i k 1 = q2f_fiveCode b) ∨
        (q2f_parentCode i k 0 = q2f_fiveCode b ∧ q2f_parentCode i k 1 = q2f_fiveCode a) := by
  decide +kernel

lemma q2f_super_complete : ∀ m : Fin 128, q2f_missingTriple ⊂ cap7_decode m →
    ∃ k : Fin 15, q2f_superCode k = m := by decide +kernel

lemma q2f_parent_good : ∀ i : Fin 3, ∀ k : Fin 10, ∀ side : Fin 2,
    2 ≤ (cap7_decode (q2f_parentCode i k side)).card ∧
      ((cap7_decode (q2f_parentCode i k side)).card = 2 →
        cap7_decode (q2f_parentCode i k side) ⊆ q2f_triple i) := by decide +kernel

lemma q2f_triple_card : ∀ i : Fin 3, (q2f_triple i).card = 3 := by decide +kernel
lemma q2f_super_card : ∀ k : Fin 15, 4 ≤ (cap7_decode (q2f_superCode k)).card := by decide +kernel

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
  · rw [decodeS]
    have hcard : 4 ≤ S.card := by simpa only [decodeS] using q2f_super_card s
    exact ⟨hS,large _ (by omega)⟩
  · exact parentGood 0 a 0 ha0
  · exact parentGood 0 a 1 ha1
  · exact parentGood 1 b 0 hb0
  · exact parentGood 1 b 1 hb1
  · exact parentGood 2 c 0 hc0
  · exact parentGood 2 c 1 hc1


end PEqualNP.Outside.L_meta_6659_aux
