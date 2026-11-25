import NineCircuitFloor
import ReaderBound

namespace PEqualNP.Outside.L_meta_1884.ConcreteReaderBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma cofactor_eq (x : Fin 9 → Bool) :
    ReaderBound.p9 x = PEqualNP.Outside.L_meta_2590.Mono18.edge x := by
  simp [ReaderBound.p9, PEqualNP.Outside.L_meta_2590.Mono18.edge, Bool.or_assoc]
  rfl

theorem sixteen_plus_readers (C : Circuit) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) = ReaderBound.p10 x) :
    16 + C.gates.countP ReaderBound.r0 ≤ C.size := by
  apply ReaderBound.main ?_ C hmono hcomp
  intro D hD hcompD
  apply NineCircuitFloor.nine_circuit_floor D hD
  intro x
  exact (hcompD x).trans (cofactor_eq x)

theorem at_most_two_readers (C : Circuit) (hmono : Monotone2 C) (hsize : C.size ≤ 18)
    (hcomp : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x ++ [!x 0]) = ReaderBound.p10 x) :
    C.gates.countP ReaderBound.r0 ≤ 2 := by
  have h := sixteen_plus_readers C hmono hcomp
  omega

end PEqualNP.Outside.L_meta_1884.ConcreteReaderBound
