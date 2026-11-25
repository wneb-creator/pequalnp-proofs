namespace PEqualNP.Outside.L_meta_2592_aux.Stronger

lemma gate_count_partition (C : PEqualNP.CircuitLowerBounds.Circuit) :
    C.gates.countP (fun g => !Extended.isNot g) + PEqualNP.NotBracket.notCount C = C.size := by
  have sameNot :
      (fun g : PEqualNP.CircuitLowerBounds.Gate => @decide
        (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
        (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op PEqualNP.CircuitLowerBounds.GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  have negSame : (fun g : PEqualNP.CircuitLowerBounds.Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change C.gates.countP (fun g => !Extended.isNot g) +
    (C.gates.filter (fun g => @decide (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
      (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op PEqualNP.CircuitLowerBounds.GateOp.not))).length = C.gates.length
  rw [sameNot, ← List.countP_eq_length_filter]
  omega

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma first_or_bank_card (j : Fin 2) : ((CanonicalBank.bank 1 j).toFinset).card = 11 := by
  fin_cases j <;> decide +kernel

lemma two_not_structure (C : PEqualNP.CircuitLowerBounds.Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C) (budget : C.size ≤ 19)
    (nots : PEqualNP.NotBracket.notCount C = 2)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    C.size = 19 ∧ C.gates.countP (fun g => !Extended.isNot g) = 17 ∧
      ∃ (S : Finset Extended.Sig), Extended.Live true Extended.target 17 S ∧
        (∀ a ∈ S, a ∈ Extended.pins) ∧
        ∃ (a b : Fin 10) (T : Finset Extended.Sig), a ≠ b ∧
          Extended.Live true Extended.target 16 T ∧
          Extended.bin 1 (Extended.pins.getD a.val Extended.zero)
            (Extended.pins.getD b.val Extended.zero) ∈ T ∧
          (∀ v ∈ T, v ∈ Extended.pins ++
            [Extended.bin 1 (Extended.pins.getD a.val Extended.zero)
              (Extended.pins.getD b.val Extended.zero)]) ∧
          ∃ j : Fin 2,
            Extended.Live true Extended.target 16 (CanonicalBank.bank 1 j).toFinset ∧
            ((CanonicalBank.bank 1 j).toFinset).card = 11 := by
  have lower := seventeen_binary_floor C fan correct
  have partition := gate_count_partition C
  have exact_size : C.size = 19 := by omega
  have exact_binary : C.gates.countP (fun g => !Extended.isNot g) = 17 := by omega
  obtain ⟨k,S,hk,run,raw⟩ := Extended.realizeRawPins C fan correct
  have min_run := seventeen_of_raw_pins run raw
  have eqk : k = 17 := by omega
  subst k
  obtain large | ⟨n,a,b,T,hn,hab,tail,used,bank⟩ := Extended.first_binary_or_eighteen run raw
  · omega
  have eqn : n = 16 := by omega
  subst n
  obtain ⟨j,U,runU,usedU,bankU⟩ := Extended.canonicalize_first_used 1 a b hab tail used bank
  have exactU := CanonicalBank.exact_bank 1 j runU bankU usedU
  refine ⟨exact_size,exact_binary,S,run,raw,a,b,T,hab,tail,used,bank,j,?_,first_or_bank_card j⟩
  exact exactU ▸ runU

end PEqualNP.Outside.L_meta_2592_aux.Stronger
