import NineGeneralFloor
import GeneralReaderBound

namespace PEqualNP.Outside.L_meta_1884.GeneralConcreteReaderBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma cofactor_eq (x : Fin 9 → Bool) :
    GeneralReaderBound.p9 x = PEqualNP.Outside.L_meta_2590.Mono18.edge x := by
  simp [GeneralReaderBound.p9, PEqualNP.Outside.L_meta_2590.Mono18.edge, Bool.or_assoc]
  rfl

theorem sixteen_plus_readers (C : Circuit) (hlegal : FanInTwo C)
    (hcomp : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) = GeneralReaderBound.p10 x) :
    16 + C.gates.countP GeneralReaderBound.r0 ≤ C.size := by
  apply GeneralReaderBound.main ?_ C hlegal hcomp
  intro D hD hcompD
  apply NineGeneralFloor.nine_circuit_floor D hD
  intro x
  exact (hcompD x).trans (cofactor_eq x)

theorem at_most_two_readers (C : Circuit) (hlegal : FanInTwo C) (hsize : C.size ≤ 18)
    (hcomp : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) = GeneralReaderBound.p10 x) :
    C.gates.countP GeneralReaderBound.r0 ≤ 2 := by
  have h := sixteen_plus_readers C hlegal hcomp
  omega

end PEqualNP.Outside.L_meta_1884.GeneralConcreteReaderBound
