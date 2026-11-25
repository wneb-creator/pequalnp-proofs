namespace PEqualNP.Outside.L_meta_2592_aux.Stronger

lemma seventeen_of_raw_pins {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins) : 17 ≤ k := by
  obtain ⟨n,a,b,d,T,eqk,ha,hb,hab,hd,tail,bank⟩ := Extended.first_proper_binary run raw
  have hlist : List.ofFn (fun i : Fin 10 => Extended.pins.getD i.val Extended.zero) =
      Extended.pins := rfl
  rw [← hlist] at ha hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hb
  have hij : i ≠ j := by
    intro eqij
    exact hab (congrArg (fun v : Fin 10 => Extended.pins.getD v.val Extended.zero) eqij)
  obtain ⟨v,U,tail',bank'⟩ := Extended.canonicalize_first ⟨d,hd⟩ i j hij tail bank
  have lower := CanonicalBank.lower ⟨d,hd⟩ v tail' bank'
  omega

lemma seventeen_binary_floor (C : PEqualNP.CircuitLowerBounds.Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k,S,hk,run,raw⟩ := Extended.realizeRawPins C fan correct
  have floor := seventeen_of_raw_pins run raw
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
  change 17 + (C.gates.filter (fun g => @decide
    (g.op = PEqualNP.CircuitLowerBounds.GateOp.not)
    (PEqualNP.CircuitLowerBounds.lineDegreeGateOpDecEq g.op PEqualNP.CircuitLowerBounds.GateOp.not))).length ≤ C.gates.length
  rw [sameNot, ← List.countP_eq_length_filter]
  omega

lemma three_not_exclusion (C : PEqualNP.CircuitLowerBounds.Circuit)
    (fan : PEqualNP.MetaComplexity.FanInTwo C)
    (budget : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ¬ ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) =
      (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
       x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
       x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
  intro correct
  have lower := seventeen_binary_floor C fan correct
  omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger
