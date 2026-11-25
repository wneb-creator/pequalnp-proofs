import Seventeen

namespace PEqualNP.Outside.L_meta_2592_aux
open PEqualNP.CircuitLowerBounds

namespace Seventeen

lemma seventeen_first_or {S : Finset Extended.Sig}
    (run : Extended.Live true Extended.target 17 S)
    (raw : ∀ a ∈ S, a ∈ Extended.pins) :
    ∃ (U : Finset Extended.Sig) (a b : Extended.Sig),
      S = insert a (insert b U) ∧ a ≠ b ∧ a ∈ U ∧ b ∈ U ∧
      Extended.bin 1 a b ∉ S ∧
      Extended.Live true Extended.target 16 (insert (Extended.bin 1 a b) U) := by
  obtain ⟨U,a,b,d,hd,rfl,_,_,hab,fresh,tail⟩ := run
  have op : d = 1 := by
    by_contra other
    have bound := after_first_nonOr_bound hd hab other fresh raw tail
    norm_num at bound
  subst d
  have retainedA := first_retained hd hab raw tail
  have swapped : Extended.bin 1 a b = Extended.bin 1 b a := by
    simp [Extended.bin,BitVec.or_comm]
  have raw' : ∀ v ∈ insert b (insert a U), v ∈ Extended.pins := by
    intro v hv
    exact raw v (by simpa only [Finset.insert_comm] using hv)
  have tail' : Extended.Live true Extended.target 16 (insert (Extended.bin 1 b a) U) :=
    swapped ▸ tail
  have retainedB := first_retained hd hab.symm raw' tail'
  exact ⟨U,a,b,rfl,hab,retainedA,retainedB,fresh,tail⟩

end Seventeen

lemma tight_two_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    C.size = 19 ∧ PEqualNP.NotBracket.notCount C = 2 ∧
    C.gates.countP (fun g => !Extended.isNot g) = 17 ∧
    ∃ S : Finset Extended.Sig, Extended.Live true Extended.target 17 S ∧
      (∀ a ∈ S, a ∈ Extended.pins) := by
  obtain ⟨k,S,hk,run,raw⟩ := Extended.realize C legal computes
  have floor := Seventeen.atLeastSeventeen run raw
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  have notCount : PEqualNP.NotBracket.notCount C = C.gates.countP Extended.isNot := by
    rw [PEqualNP.NotBracket.notCount, sameNot, List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) = (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame, ←notCount] at count
  change C.size = _ at count
  have exactK : k = 17 := by omega
  have exactBinary : C.gates.countP (fun g => !Extended.isNot g) = 17 := by omega
  refine ⟨by omega,by omega,exactBinary,S,?_,raw⟩
  simpa only [exactK] using run

lemma tight_two_not_first_or (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    C.size = 19 ∧ PEqualNP.NotBracket.notCount C = 2 ∧
    C.gates.countP (fun g => !Extended.isNot g) = 17 ∧
    ∃ (U : Finset Extended.Sig) (a b : Extended.Sig),
      (∀ v ∈ insert a (insert b U), v ∈ Extended.pins) ∧
      a ≠ b ∧ a ∈ U ∧ b ∈ U ∧
      Extended.bin 1 a b ∉ insert a (insert b U) ∧
      Extended.Live true Extended.target 16 (insert (Extended.bin 1 a b) U) := by
  obtain ⟨size,nots,binary,S,run,raw⟩ := tight_two_not C legal small many computes
  obtain ⟨U,a,b,rfl,diff,retainedA,retainedB,fresh,tail⟩ :=
    Seventeen.seventeen_first_or run raw
  exact ⟨size,nots,binary,U,a,b,raw,diff,retainedA,retainedB,fresh,tail⟩

end PEqualNP.Outside.L_meta_2592_aux
