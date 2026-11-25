import PEqualNP.Outside.L_meta_6581

namespace PEqualNP.Outside.Pilot113GlobalCount

open PEqualNP.Outside.L_meta_6581 PEqualNP.CircuitLowerBounds

lemma atLeastSeventeen (hNineFloor : Lower true inputs graph 15)
    {k : Nat} {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  apply Pilot113FirstStep.all_first_steps_floor (run := run) (raw := raw)
  intro n U i j d hij hd hraw htail
  rcases Extended.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · have bound := Pilot113GlobalAnd.first_and_eighteen hNineFloor
      0 (Or.inl rfl) i j hij hraw htail
    omega
  · exact Pilot113GlobalOr.first_or_seventeen hNineFloor i j hij hraw htail
  · have bound := Pilot113GlobalAnd.first_and_eighteen hNineFloor
      2 (Or.inr rfl) i j hij hraw htail
    omega
  · have flip : Extended.bin 3 (Pilot113FirstStep.pin i) (Pilot113FirstStep.pin j) =
        Extended.bin 2 (Pilot113FirstStep.pin j) (Pilot113FirstStep.pin i) := by
      simp [Extended.bin, BitVec.and_comm]
    rw [flip] at htail
    have bound := Pilot113GlobalAnd.first_and_eighteen hNineFloor
      2 (Or.inr rfl) j i (Ne.symm hij) hraw htail
    omega

lemma nonNot_seventeen (hNineFloor : Lower true inputs graph 15)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 ≤ C.gates.countP (fun g => !Extended.isNot g) := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  exact le_trans (atLeastSeventeen hNineFloor run raw) hk

lemma three_not_impossible (hNineFloor : Lower true inputs graph 15)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ Extended.f10 x := by
  by_contra! computes
  have floor := nonNot_seventeen hNineFloor C legal computes
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter] at many
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) =
      (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change C.gates.length ≤ 19 at small
  omega

end PEqualNP.Outside.Pilot113GlobalCount
