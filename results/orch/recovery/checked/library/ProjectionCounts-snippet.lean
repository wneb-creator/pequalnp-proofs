namespace PEqualNP.Outside.L_meta_2592.FormulaPruning

open PEqualNP.MetaComplexity

lemma occursOpt_joinProjection (isOr : Bool) (a b : Option (DMFormula 3)) (j : Fin 3) :
    occursOpt (joinProjection isOr a b) j = occursOpt a j + occursOpt b j := by
  cases a <;> cases b <;> cases isOr <;> simp [joinProjection, occursOpt, occurs]

lemma occurs_project_unique {n : Nat} (ρ : Fin n → Option (Fin 3))
    (φ : DMFormula n) (i : Fin n) (j : Fin 3)
    (unique : ∀ k, ρ k = some j ↔ k = i) :
    occursOpt (project ρ φ) j = occurs φ i := by
  induction φ with
  | lit k b =>
    cases value : ρ k with
    | none =>
      have different : k ≠ i := by
        intro same
        have hit := (unique k).mpr same
        simp [value] at hit
      simp [project, value, occursOpt, occurs, different]
    | some l =>
      have same : l = j ↔ k = i := by simpa only [value, Option.some.injEq] using unique k
      simp [project, value, occursOpt, occurs, same]
  | and a b ha hb =>
    simp only [project, occursOpt_joinProjection, occurs, ha, hb]
  | or a b ha hb =>
    simp only [project, occursOpt_joinProjection, occurs, ha, hb]

lemma leavesOpt_eq_sum_occursOpt (a : Option (DMFormula 3)) :
    leavesOpt a = ∑ j, occursOpt a j := by
  cases a with
  | none => simp [leavesOpt, occursOpt]
  | some φ => simpa only [leavesOpt, occursOpt] using (sum_occurs φ).symm

lemma projected_leaves_eq_three_occurrences {n : Nat}
    (ρ : Fin n → Option (Fin 3)) (φ : DMFormula n) (a b c : Fin n)
    (ha : ∀ k, ρ k = some 0 ↔ k = a)
    (hb : ∀ k, ρ k = some 1 ↔ k = b)
    (hc : ∀ k, ρ k = some 2 ↔ k = c) :
    leavesOpt (project ρ φ) = occurs φ a + occurs φ b + occurs φ c := by
  rw [leavesOpt_eq_sum_occursOpt]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  change occursOpt (project ρ φ) 0 + (occursOpt (project ρ φ) 1 +
    occursOpt (project ρ φ) 2) = _
  rw [occurs_project_unique ρ φ a 0 ha, occurs_project_unique ρ φ b 1 hb,
    occurs_project_unique ρ φ c 2 hc]
  omega

end PEqualNP.Outside.L_meta_2592.FormulaPruning
