import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.Structural

open PEqualNP.CircuitLowerBounds

def columnExample : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.or, [11, 5]⟩, ⟨.and, [10, 12]⟩, ⟨.not, [13]⟩,
    ⟨.or, [14, 7]⟩, ⟨.and, [15, 5]⟩, ⟨.or, [16, 8]⟩, ⟨.or, [17, 7]⟩,
    ⟨.or, [18, 6]⟩, ⟨.or, [19, 3]⟩, ⟨.and, [20, 2]⟩, ⟨.or, [21, 6]⟩,
    ⟨.or, [22, 2]⟩, ⟨.or, [23, 20]⟩, ⟨.and, [24, 9]⟩, ⟨.or, [25, 3]⟩,
    ⟨.and, [26, 19]⟩, ⟨.and, [27, 9]⟩], 28⟩

lemma columnExample_model :
    PEqualNP.MetaComplexity.FanInTwo columnExample ∧ columnExample.size = 18 ∧
    (∀ g ∈ columnExample.gates, 0 ∉ g.inputs) ∧
    columnExample.gates.countP (fun g => match g.op with | .not => true | _ => false) = 1 ∧
    columnExample.gates.countP (fun g => g.inputs.contains 10) = 1 := by
  simp [PEqualNP.MetaComplexity.FanInTwo, columnExample, Circuit.size]

lemma columnExample_chain : columnExample.output = 28 ∧
    ∀ j ∈ List.range 17,
      11 + j ∈ (columnExample.gates.getD (j + 1) ⟨.or, []⟩).inputs := by
  decide +kernel

lemma columnExample_trace :
    (columnExample.wires (List.replicate 10 false ++ [true])).getD 13 false = false ∧
    ∀ i ∈ ([1, 4, 5] : List (Fin 10)),
      (columnExample.wires
        (List.ofFn (fun j : Fin 10 => decide (j = i)) ++ [true])).getD 14 false = false ∧
      (columnExample.wires
        (List.ofFn (fun j : Fin 10 => decide (j = 0 ∨ j = i)) ++ [false])).getD 14 false = true := by
  decide +kernel

lemma columnExample_misses_edge :
    columnExample.eval
      (List.ofFn (fun j : Fin 10 => decide (j = 0 ∨ j = 1)) ++ [false]) = false := by
  decide +kernel

def petersenExpression (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma columnExample_not_petersen :
    let x : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
    columnExample.eval (List.ofFn x ++ [!x 0]) ≠ petersenExpression x := by
  decide +kernel

end PEqualNP.Outside.L_meta_1884_aux.Structural
