lemma first_binary_split (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    ∃ (k : ℕ) (U : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      k + 1 ≤ C.gates.countP (fun g => !Extended.isNot g) ∧ d < 4 ∧
      a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      Extended.Live true Extended.target k (insert (Extended.bin d a b) U) ∧
      ∀ v ∈ U, v ∈ Extended.initial := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  cases k with
  | zero =>
      obtain ⟨rfl, hp⟩ := run
      have hmem := raw Extended.target (by simp)
      have hn : Extended.target ∉ Extended.initial := by decide +kernel
      exact False.elim (hn hmem)
  | succ k =>
      obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩ := run
      have hd4 : d < 4 := by
        rcases hd with hd | ⟨hu, hd⟩ <;> omega
      exact ⟨k, U, a, b, d, hk, hd4, raw a (by simp), raw b (by simp), hab,
        tail, fun v hv => raw v (by simp [hv])⟩

lemma binary_floor17_of_suffix
    (suffix : ∀ (k : ℕ) (S : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      d < 4 → a ∈ Extended.initial → b ∈ Extended.initial → a ≠ b →
      Extended.Live true Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin d a b]) → 16 ≤ k)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k, U, a, b, d, hk, hd, ha, hb, hab, tail, raw⟩ :=
    first_binary_split C legal computes
  have floor : 16 ≤ k := by
    apply suffix k (insert (Extended.bin d a b) U) a b d hd ha hb hab tail
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · exact List.mem_append_left _ (raw v hv)
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) = (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change 17 + C.gates.countP Extended.isNot ≤ C.gates.length
  omega
