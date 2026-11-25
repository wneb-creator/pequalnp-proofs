lemma first_binary_or_of_binary_le_seventeen
    (suffix : ∀ (k : ℕ) (S : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      d < 4 → d ≠ 1 → a ∈ Extended.initial → b ∈ Extended.initial → a ≠ b →
      Extended.Live true Extended.target k S → Extended.bin d a b ∈ S →
      (∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin d a b]) → 17 ≤ k)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x)
    (small : C.gates.countP (fun g => !Extended.isNot g) ≤ 17) :
    ∃ (k : ℕ) (U : Finset Extended.Sig) (a b : Extended.Sig),
      k + 1 ≤ C.gates.countP (fun g => !Extended.isNot g) ∧
      a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      Extended.Live true Extended.target k (insert (Extended.bin 1 a b) U) ∧
      ∀ v ∈ U, v ∈ Extended.initial := by
  obtain ⟨k, U, a, b, d, hk, hd, ha, hb, hab, tail, raw⟩ :=
    first_binary_split C legal computes
  have hd1 : d = 1 := by
    by_contra hd1
    have floor : 17 ≤ k := by
      apply suffix k (insert (Extended.bin d a b) U) a b d hd hd1 ha hb hab tail
      · simp
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · simp
        · exact List.mem_append_left _ (raw v hv)
    omega
  subst d
  exact ⟨k, U, a, b, hk, ha, hb, hab, tail, raw⟩

lemma binary_count_le_seventeen_of_two_nots (C : Circuit) (small : C.size ≤ 19)
    (two : 2 ≤ PEqualNP.NotBracket.notCount C) :
    C.gates.countP (fun g => !Extended.isNot g) ≤ 17 := by
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter] at two
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) = (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change C.gates.length ≤ 19 at small
  omega
