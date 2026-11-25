namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

lemma literal_table_lt : ∀ (i : Fin 3) (b : Bool), literalTable i b < 256 := by
  decide +kernel

lemma table_high_false {t i : Nat} (ht : t < 256) (hi : 8 ≤ i) : t.testBit i = false := by
  change t < 2 ^ 8 at ht
  exact Nat.testBit_lt_two_pow (ht.trans_le (Nat.pow_le_pow_right (by decide) hi))

lemma pruning_table_lt (φ : DMFormula 3) : ∀ t ∈ pruningTables φ, t < 256 := by
  induction φ with
  | lit i b =>
    intro t ht
    simp [pruningTables] at ht
    rcases ht with rfl | rfl | rfl
    · decide
    · decide
    · exact literal_table_lt i b
  | and a b ha hb =>
    intro t ht
    simp only [pruningTables, List.mem_eraseDups, List.mem_append] at ht
    rcases ht with ht | ht
    · have : t = 0 ∨ t = 255 := by simpa using ht
      rcases this with rfl | rfl <;> decide
    · obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp ht
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv
      change Nat.land u v < 2 ^ 8
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      simp [table_high_false (ha u hu) hi, table_high_false (hb v hv) hi]
  | or a b ha hb =>
    intro t ht
    simp only [pruningTables, List.mem_eraseDups, List.mem_append] at ht
    rcases ht with ht | ht
    · have : t = 0 ∨ t = 255 := by simpa using ht
      rcases this with rfl | rfl <;> decide
    · obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp ht
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hv
      change Nat.lor u v < 2 ^ 8
      apply Nat.lt_pow_two_of_testBit
      intro i hi
      simp [table_high_false (ha u hu) hi, table_high_false (hb v hv) hi]

lemma tablesOpt_lt (a : Option (DMFormula 3)) {t : Nat} (ht : t ∈ tablesOpt a) : t < 256 := by
  cases a with
  | none =>
    have : t = 0 ∨ t = 255 := by simpa [tablesOpt] using ht
    rcases this with rfl | rfl <;> decide
  | some a => exact pruning_table_lt a t ht

lemma table_eq_of_bits {t u : Nat} (ht : t < 256) (hu : u < 256)
    (heq : ∀ r : Fin 8, t.testBit r.val = u.testBit r.val) : t = u := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 8
  · exact heq ⟨i, hi⟩
  · rw [table_high_false ht (by omega), table_high_false hu (by omega)]

lemma project_mem_of_cofactor {n : Nat} (ρ : Fin n → Option (Fin 3))
    (base : Fin n → Bool) (φ : DMFormula n) {t : Nat} (ht : t < 256)
    (heq : ∀ r : Fin 8, φ.eval (cofactorInput ρ base r) = t.testBit r.val) :
    t ∈ tablesOpt (project ρ φ) := by
  obtain ⟨u, hu, hbits⟩ := project_realizes ρ base φ
  have same : u = t := table_eq_of_bits (tablesOpt_lt _ hu) ht
    (fun r => (hbits r).symm.trans (heq r))
  simpa [same] using hu

end PEqualNP.Outside.L_meta_2592.FormulaPruning
