import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.AntiDiagonal

open PEqualNP.CircuitLowerBounds

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def input (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
  match i.val with
  | 0 => x 0
  | 1 => x 1
  | 2 => !(x 0)
  | 3 => x 2
  | 4 => x 3
  | 5 => x 4
  | 6 => x 5
  | 7 => x 6
  | 8 => x 7
  | _ => x 8

def circuit : Circuit :=
  ⟨[⟨.not, [0]⟩,
    ⟨.or, [0, 7]⟩, ⟨.or, [9, 7]⟩,
    ⟨.or, [0, 8]⟩, ⟨.or, [9, 8]⟩,
    ⟨.or, [7, 8]⟩,
    ⟨.and, [4, 10]⟩, ⟨.and, [2, 11]⟩,
    ⟨.and, [3, 12]⟩, ⟨.and, [6, 13]⟩,
    ⟨.and, [5, 14]⟩,
    ⟨.or, [1, 15]⟩, ⟨.or, [20, 16]⟩,
    ⟨.or, [21, 17]⟩, ⟨.or, [22, 18]⟩,
    ⟨.or, [23, 19]⟩], 24⟩

lemma fanInTwo : PEqualNP.MetaComplexity.FanInTwo circuit := by
  simp [PEqualNP.MetaComplexity.FanInTwo, circuit]

lemma size : circuit.size = 16 := rfl

lemma oneNot : PEqualNP.NotBracket.notCount circuit = 1 := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma computes : ∀ x : Fin 9 → Bool,
    circuit.eval (List.ofFn x) = petersen (input x) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.AntiDiagonal
