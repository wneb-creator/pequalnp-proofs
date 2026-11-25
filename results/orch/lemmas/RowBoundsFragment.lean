namespace PEqualNP.Outside.L_meta_2602_aux.RowBounds

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

def rowSet (r : Nat) : Finset (Fin 26) :=
  Finset.univ.filter (fun v => r.testBit v.val = true)

lemma mem_rowSet (r : Nat) (v : Fin 26) :
    v ∈ rowSet r ↔ r.testBit v.val = true := by simp [rowSet]

def Correct (C : AndCountCircuit 26) : Prop :=
  ∀ U : Finset (Fin 26), C.eval U = true ↔
    ∃ p l : Fin 13, (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) ∧
      Fin.castAdd 13 p ∈ U ∧ Fin.natAdd 13 l ∈ U

lemma row_facts (r : Nat) (hr : r ∈ FalseRows.rows) :
    r < 2^26 ∧
    (∀ p l : Fin 13, FalseRows.inc p.val l.val = true →
      ¬ (r.testBit p.val = true ∧ r.testBit (13+l.val) = true)) ∧
    (∀ p : Fin 13, r.testBit p.val = false →
      ∃ l : Fin 13, FalseRows.inc p.val l.val = true ∧ r.testBit (13+l.val) = true) ∧
    (∀ l : Fin 13, r.testBit (13+l.val) = false →
      ∃ p : Fin 13, FalseRows.inc p.val l.val = true ∧ r.testBit p.val = true) := by
  have h := List.all_eq_true.mp FalseRows.rows_valid.2.2 r hr
  simp only [FalseRows.rowOK, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨hbound, hfalse⟩, hpoint⟩, hline⟩
  refine ⟨hbound, ?_, ?_, ?_⟩
  · intro p l hi hb
    have hp := List.all_eq_true.mp hfalse p.val (List.mem_range.mpr p.isLt)
    have hl := List.all_eq_true.mp hp l.val (List.mem_range.mpr l.isLt)
    simp [hi, hb.1, hb.2] at hl
  · intro p hp
    have h := List.all_eq_true.mp hpoint p.val (List.mem_range.mpr p.isLt)
    simp only [hp, Bool.false_or] at h
    obtain ⟨l, hl, hval⟩ := List.any_eq_true.mp h
    exact ⟨⟨l,List.mem_range.mp hl⟩, by simpa only [Bool.and_eq_true] using hval⟩
  · intro l hl
    have h := List.all_eq_true.mp hline l.val (List.mem_range.mpr l.isLt)
    simp only [hl, Bool.false_or] at h
    obtain ⟨p, hp, hval⟩ := List.any_eq_true.mp h
    exact ⟨⟨p,List.mem_range.mp hp⟩, by simpa only [Bool.and_eq_true] using hval⟩

lemma rowSet_injective {r s : Nat} (hr : r < 2^26) (hs : s < 2^26)
    (he : rowSet r = rowSet s) : r = s := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 26
  · have hm : r.testBit i = true ↔ s.testBit i = true := by
      have ht : (⟨i,hi⟩ : Fin 26) ∈ rowSet r ↔ (⟨i,hi⟩ : Fin 26) ∈ rowSet s := by rw [he]
      simpa only [mem_rowSet] using ht
    cases hri : r.testBit i <;> cases hsi : s.testBit i <;> simp_all
  · have hp : 2^26 ≤ 2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hr hp),
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hs hp)]

lemma separates (C : AndCountCircuit 26) (hC : Correct C)
    (r : Nat) (hr : r ∈ FalseRows.rows) :
    C.eval (rowSet r) = false ∧
      ∀ v, v ∉ rowSet r → C.eval (insert v (rowSet r)) = true := by
  have hf := row_facts r hr
  constructor
  · apply Bool.eq_false_iff.mpr
    intro he
    obtain ⟨p,l,hi,hp,hl⟩ := (hC (rowSet r)).mp he
    exact hf.2.1 p l ((FalseRows.incidence_correct p l).mpr hi)
      ⟨(mem_rowSet r _).mp hp, (mem_rowSet r _).mp hl⟩
  · intro v hv
    have hb : r.testBit v.val = false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      exact hv ((mem_rowSet r v).mpr ht)
    apply (hC (insert v (rowSet r))).mpr
    by_cases hleft : v.val < 13
    · let p : Fin 13 := ⟨v.val,hleft⟩
      obtain ⟨l,hi,hl⟩ := hf.2.2.1 p hb
      have hvp : Fin.castAdd 13 p = v := Fin.ext rfl
      refine ⟨p,l,(FalseRows.incidence_correct p l).mp hi, ?_, ?_⟩
      · rw [hvp]
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem ((mem_rowSet r _).mpr hl)
    · let l : Fin 13 := ⟨v.val-13,by omega⟩
      have hvl : Fin.natAdd 13 l = v := by apply Fin.ext; simp only [Fin.natAdd, l]; omega
      have hbl : r.testBit (13+l.val) = false := by
        have he : 13+l.val = v.val := by dsimp [l]; omega
        simpa [he] using hb
      obtain ⟨p,hi,hp⟩ := hf.2.2.2 l hbl
      refine ⟨p,l,(FalseRows.incidence_correct p l).mp hi, ?_, ?_⟩
      · exact Finset.mem_insert_of_mem ((mem_rowSet r _).mpr hp)
      · rw [hvl]
        exact Finset.mem_insert_self _ _

def selectedRows (S : Finset (Fin 26)) : List Nat :=
  FalseRows.rows.filter (fun r => decide (S ⊆ rowSet r))

lemma selected_mem {S : Finset (Fin 26)} {r : Nat} (h : r ∈ selectedRows S) :
    r ∈ FalseRows.rows ∧ S ⊆ rowSet r := by
  simpa [selectedRows] using h

theorem information (C : AndCountCircuit 26) (hC : Correct C) (S : Finset (Fin 26)) :
    (selectedRows S).length ≤ 2 ^ (FreeRows.Free C S).card := by
  let R := (selectedRows S).toFinset
  have hbound := FreeRows.row_bound C (fun r : ↥R => rowSet r.val) S
    (by
      intro r s he
      apply Subtype.ext
      exact rowSet_injective
        (row_facts r.val (selected_mem (List.mem_toFinset.mp r.property)).1).1
        (row_facts s.val (selected_mem (List.mem_toFinset.mp s.property)).1).1 he)
    (fun r => (selected_mem (List.mem_toFinset.mp r.property)).2)
    (fun r => separates C hC r.val (selected_mem (List.mem_toFinset.mp r.property)).1)
  have hcard : Fintype.card ↥R = (selectedRows S).length := by
    rw [Fintype.card_coe]
    exact List.toFinset_card_of_nodup (FalseRows.rows_valid.2.1.filter _)
  simpa only [hcard] using hbound

def Occ (C : AndCountCircuit 26) (S : Finset (Fin 26)) : Finset (Fin C.size) :=
  Finset.univ \ FreeRows.Free C S

lemma mem_occ_singleton (C : AndCountCircuit 26) (v : Fin 26) (i : Fin C.size) :
    i ∈ Occ C {v} ↔ v ∈ C.leftVars i ∨ v ∈ C.rightVars i := by
  simp [Occ, FreeRows.Free] <;> tauto

lemma occ_balance (C : AndCountCircuit 26) (S : Finset (Fin 26)) :
    (Occ C S).card + (FreeRows.Free C S).card = C.size := by
  simpa [Occ] using Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ (FreeRows.Free C S))

lemma occ_pair (C : AndCountCircuit 26) (v w : Fin 26) :
    Occ C {v,w} = Occ C {v} ∪ Occ C {w} := by
  ext i
  simp [Occ, FreeRows.Free] <;> tauto

theorem size_ge_ten (C : AndCountCircuit 26) (hC : Correct C) : 10 ≤ C.size := by
  have h : 704 ≤ 2^C.size := by
    simpa [selectedRows, FreeRows.Free, FalseRows.rows_length] using information C hC ∅
  by_contra hn
  have hp : 2^C.size ≤ 2^9 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hp
  omega

lemma occ_le_of_count (C : AndCountCircuit 26) (hC : Correct C)
    (hsize : C.size ≤ 12) (S : Finset (Fin 26)) (b : Nat)
    (hb : 2^(11-b) < (selectedRows S).length) (hb12 : b ≤ 11) :
    (Occ C S).card ≤ b := by
  have hi := information C hC S
  have hbal := occ_balance C S
  by_contra hbad
  have hfree : (FreeRows.Free C S).card ≤ 11-b := by omega
  have hp : 2^(FreeRows.Free C S).card ≤ 2^(11-b) :=
    Nat.pow_le_pow_right (by decide) hfree
  omega

lemma singleton_count (v : Fin 26) : (selectedRows {v}).length = 197 := by
  simpa [selectedRows, rowSet] using FalseRows.through_one v

lemma same_point_count (p q : Fin 13) (hpq : p ≠ q) :
    (selectedRows {Fin.castAdd 13 p,Fin.castAdd 13 q}).length = 52 := by
  simpa [selectedRows, rowSet, Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Bool.and_eq_true] using (FalseRows.through_same p q hpq).1

lemma same_line_count (p q : Fin 13) (hpq : p ≠ q) :
    (selectedRows {Fin.natAdd 13 p,Fin.natAdd 13 q}).length = 52 := by
  simpa [selectedRows, rowSet, Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Bool.and_eq_true, Nat.add_comm] using (FalseRows.through_same p q hpq).2

lemma cross_count (p l : Fin 13) (hpl : FalseRows.inc p.val l.val = false) :
    (selectedRows {Fin.castAdd 13 p,Fin.natAdd 13 l}).length = 70 := by
  simpa [selectedRows, rowSet, Finset.insert_subset_iff, Finset.singleton_subset_iff,
    Bool.and_eq_true, Nat.add_comm] using FalseRows.through_cross p l hpl

theorem occurrence_width (C : AndCountCircuit 26) (hC : Correct C) (hsize : C.size ≤ 12)
    (v : Fin 26) : (Occ C {v}).card ≤ 4 := by
  apply occ_le_of_count C hC hsize {v} 4
  · rw [singleton_count]
    decide
  · decide

theorem same_point_union (C : AndCountCircuit 26) (hC : Correct C) (hsize : C.size ≤ 12)
    (p q : Fin 13) (hpq : p ≠ q) :
    (Occ C {Fin.castAdd 13 p} ∪ Occ C {Fin.castAdd 13 q}).card ≤ 6 := by
  rw [← occ_pair]
  apply occ_le_of_count C hC hsize _ 6
  · rw [same_point_count p q hpq]
    decide
  · decide

theorem same_line_union (C : AndCountCircuit 26) (hC : Correct C) (hsize : C.size ≤ 12)
    (p q : Fin 13) (hpq : p ≠ q) :
    (Occ C {Fin.natAdd 13 p} ∪ Occ C {Fin.natAdd 13 q}).card ≤ 6 := by
  rw [← occ_pair]
  apply occ_le_of_count C hC hsize _ 6
  · rw [same_line_count p q hpq]
    decide
  · decide

theorem cross_nonedge_union (C : AndCountCircuit 26) (hC : Correct C)
    (hsize : C.size ≤ 12) (p l : Fin 13) (hpl : FalseRows.inc p.val l.val = false) :
    (Occ C {Fin.castAdd 13 p} ∪ Occ C {Fin.natAdd 13 l}).card ≤ 5 := by
  rw [← occ_pair]
  apply occ_le_of_count C hC hsize _ 5
  · rw [cross_count p l hpl]
    decide
  · decide

end PEqualNP.Outside.L_meta_2602_aux.RowBounds
