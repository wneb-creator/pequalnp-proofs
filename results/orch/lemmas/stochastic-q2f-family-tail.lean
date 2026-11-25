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

