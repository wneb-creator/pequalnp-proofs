import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof.Readers

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592.BinaryFloor

lemma clean_with_total_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
      gs.length ≤ C.size ∧ ∀ x, vl gs x o = f x := by
  have hok : ∀ g ∈ C.gates, Ok g := hfan
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    refine ⟨acc.2, j, ?_, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · simpa [nonNotCount, hacc] using elim_nonNotCount n C.gates (idStats n, [])
    · simpa [hacc, Circuit.size] using elim_len n C.gates (idStats n, [])
    · intro y
      simpa only [hst, Stat.val, vl] using hval y

lemma least_with_total_budget {n : ℕ} {f : (Fin n → Bool) → Bool} (C : Circuit)
    (hfan : FanInTwo C) (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ gs o, Least n f gs o ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
      gs.length ≤ C.size := by
  classical
  let admissible (t : ℕ) := ∃ gs o, CleanL n gs ∧ nonNotCount gs ≤ nonNotCount C.gates ∧
    (∀ x, vl gs x o = f x) ∧ gs.length = t
  obtain ⟨gs, o, clean, count, total, he⟩ := clean_with_total_budget C hfan hev hnc
  have existsAdmissible : ∃ t, admissible t := ⟨gs.length, gs, o, clean, count, he, rfl⟩
  obtain ⟨gs', o', hc, hb, he', hl⟩ := Nat.find_spec existsAdmissible
  refine ⟨gs', o', ⟨hc, he', ?_⟩, hb, ?_⟩
  · intro testGates testOut testClean testEval testCost
    have lower := Nat.find_min' existsAdmissible
      (show admissible testGates.length from
        ⟨testGates, testOut, testClean, testCost.trans hb, testEval, rfl⟩)
    exact hl.trans_le lower
  · exact (hl.trans_le (Nat.find_min' existsAdmissible
      (show admissible gs.length from ⟨gs, o, clean, count, he, rfl⟩))).trans total

lemma least_fifteen_of_four_not (C : Circuit) (hfan : FanInTwo C)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersenF x)
    (hsize : C.size ≤ 19) (hnot : PEqualNP.NotBracket.notCount C = 4) :
    ∃ gs o, Least 10 petersenF gs o ∧ nonNotCount gs = 15 ∧ gs.length ≤ 19 := by
  obtain ⟨gs, o, least, count, total⟩ :=
    least_with_total_budget C hfan hev petersen_nonconstant
  have originalTotal := nonNotCount_add_notCount C.gates
  rw [not_count_eq C, hnot] at originalTotal
  have leastFan : FanInTwo ⟨gs, o⟩ := fun g hg => (clean_nok 10 gs least.hcl g hg).1
  have lower := petersen_binary_lower ⟨gs, o⟩ leastFan least.hev
  change 15 ≤ nonNotCount gs at lower
  change gs.length ≤ C.gates.length at total
  change C.gates.length ≤ 19 at hsize
  refine ⟨gs, o, least, ?_, ?_⟩ <;> omega

end PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof.Readers
