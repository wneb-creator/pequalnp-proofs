import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2870_aux.Masking

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 3]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.and, [8, 9]⟩], 10⟩

lemma size_eq : circuit.size = 7 := rfl

lemma computes_matching (x : Fin 4 → Bool) :
    circuitFun 4 circuit x = ((x 0 && x 2) || (x 1 && x 3)) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [circuitFun, Circuit.eval, Circuit.wires, circuit, GateOp.eval,
      List.ofFn_succ, h0, h1, h2, h3]

lemma first_and_false_positive :
    let x : Fin 4 → Bool := fun i => decide (i = 0 ∨ i = 3)
    (circuit.wires (List.ofFn x)).getD 6 false = true ∧
      circuitFun 4 circuit x = false ∧
      ¬ ((x 0 = true ∧ x 2 = true) ∨ (x 1 = true ∧ x 3 = true)) := by
  decide

end PEqualNP.Outside.L_meta_2870_aux.Masking
