import CombinedOrdinary

namespace PEqualNP.Outside.Pilot113GlobalSeventeen

open PEqualNP.Outside.L_meta_6581 PEqualNP.CircuitLowerBounds

theorem seventeen_nonNot (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 ≤ C.gates.countP (fun g => !Extended.isNot g) :=
  Pilot113GlobalCount.nonNot_seventeen nineFloor C legal computes

theorem three_not_impossible (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ Extended.f10 x :=
  Pilot113GlobalCount.three_not_impossible nineFloor C legal small many

end PEqualNP.Outside.Pilot113GlobalSeventeen
