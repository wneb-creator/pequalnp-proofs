import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12416

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def upperCircuit : Circuit :=
  ⟨[⟨.or, [4, 5]⟩,
    ⟨.and, [0, 1]⟩,
    ⟨.and, [0, 3]⟩,
    ⟨.and, [1, 2]⟩,
    ⟨.or, [8, 9]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [11, 6]⟩,
    ⟨.and, [10, 12]⟩,
    ⟨.or, [7, 13]⟩], 14⟩

lemma upperCircuit_mono : Monotone2 upperCircuit := by
  simp [upperCircuit, Monotone2]

lemma upperCircuit_size : upperCircuit.size = 9 := rfl

set_option maxRecDepth 100000 in
lemma upperCircuit_eval : ∀ x : Fin 6 → Bool,
    upperCircuit.eval (List.ofFn x) =
      Nat.testBit (3939035848 * 2 ^ 32 + 3939035272)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_12416
