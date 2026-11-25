namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

lemma true_table_bit (r : Fin 8) : (255 : Nat).testBit r.val = true := by
  fin_cases r <;> decide

lemma literal_table_bit : ∀ (i : Fin 3) (b : Bool) (r : Fin 8),
    (literalTable i b).testBit r.val =
      if b then r.val.testBit i.val else !r.val.testBit i.val := by
  decide +kernel

lemma constants_mem (a : Option (DMFormula 3)) :
    0 ∈ tablesOpt a ∧ 255 ∈ tablesOpt a := by
  cases a with
  | none => simp [tablesOpt]
  | some a => cases a <;> simp [tablesOpt, pruningTables]

lemma constant_realizes (a : Option (DMFormula 3)) (b : Bool) :
    realizes a (fun _ => b) := by
  cases b with
  | false => exact ⟨0, (constants_mem a).1, by intro r; simp⟩
  | true => exact ⟨255, (constants_mem a).2, fun r => (true_table_bit r).symm⟩

lemma realizes_join (a b : Option (DMFormula 3)) (f g : Fin 8 → Bool) (isOr : Bool)
    (hf : realizes a f) (hg : realizes b g) :
    realizes (joinProjection isOr a b) (fun r => if isOr then f r || g r else f r && g r) := by
  obtain ⟨u, hu, hfu⟩ := hf
  obtain ⟨v, hv, hgv⟩ := hg
  cases a with
  | none =>
    have hu' : u = 0 ∨ u = 255 := by simpa [tablesOpt] using hu
    rcases hu' with rfl | rfl
    · cases isOr with
      | false =>
        refine ⟨0, (constants_mem _).1, ?_⟩
        intro r
        simp [hfu r]
      | true =>
        refine ⟨v, ?_, ?_⟩
        · simpa [joinProjection] using hv
        · intro r; simp [hfu r, hgv r]
    · cases isOr with
      | false =>
        refine ⟨v, ?_, ?_⟩
        · simpa [joinProjection] using hv
        · intro r; simp [hfu r, hgv r, true_table_bit]
      | true =>
        refine ⟨255, (constants_mem _).2, ?_⟩
        intro r
        simp [hfu r, true_table_bit]
  | some a =>
    cases b with
    | none =>
      have hv' : v = 0 ∨ v = 255 := by simpa [tablesOpt] using hv
      rcases hv' with rfl | rfl
      · cases isOr with
        | false =>
          refine ⟨0, (constants_mem _).1, ?_⟩
          intro r; simp [hgv r]
        | true =>
          refine ⟨u, ?_, ?_⟩
          · simpa [joinProjection] using hu
          · intro r; simp [hfu r, hgv r]
      · cases isOr with
        | false =>
          refine ⟨u, ?_, ?_⟩
          · simpa [joinProjection] using hu
          · intro r; simp [hfu r, hgv r, true_table_bit]
        | true =>
          refine ⟨255, (constants_mem _).2, ?_⟩
          intro r; simp [hgv r, true_table_bit]
    | some b =>
      cases isOr with
      | false =>
        refine ⟨Nat.land u v, ?_, ?_⟩
        · simp only [joinProjection, Bool.false_eq_true, ite_false, tablesOpt, pruningTables,
            List.mem_eraseDups, List.mem_append]
          right
          exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨v, hv, rfl⟩⟩
        · intro r
          simp [hfu r, hgv r, Nat.testBit_land]
      | true =>
        refine ⟨Nat.lor u v, ?_, ?_⟩
        · simp only [joinProjection, ite_true, tablesOpt, pruningTables,
            List.mem_eraseDups, List.mem_append]
          right
          exact List.mem_flatMap.mpr ⟨u, hu, List.mem_map.mpr ⟨v, hv, rfl⟩⟩
        · intro r
          simp [hfu r, hgv r, Nat.testBit_lor]

lemma project_realizes {n : Nat} (ρ : Fin n → Option (Fin 3)) (base : Fin n → Bool)
    (φ : DMFormula n) :
    realizes (project ρ φ) (fun r => φ.eval (cofactorInput ρ base r)) := by
  induction φ with
  | lit i b =>
    cases hi : ρ i with
    | none =>
      simpa [project, hi, DMFormula.eval, cofactorInput] using
        constant_realizes none (if b then base i else !base i)
    | some j =>
      refine ⟨literalTable j b, ?_, ?_⟩
      · simp [project, hi, tablesOpt, pruningTables]
      · intro r
        simpa [DMFormula.eval, cofactorInput, hi] using (literal_table_bit j b r).symm
  | and a b ha hb =>
    simpa [project, DMFormula.eval] using realizes_join (project ρ a) (project ρ b)
      (fun r => a.eval (cofactorInput ρ base r))
      (fun r => b.eval (cofactorInput ρ base r)) false ha hb
  | or a b ha hb =>
    simpa [project, DMFormula.eval] using realizes_join (project ρ a) (project ρ b)
      (fun r => a.eval (cofactorInput ρ base r))
      (fun r => b.eval (cofactorInput ρ base r)) true ha hb

end PEqualNP.Outside.L_meta_2592.FormulaPruning
