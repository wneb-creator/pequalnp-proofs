import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_13154

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def monotoneWitness : Circuit :=
  ⟨[⟨.and, [2, 3]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [4, 5]⟩,
    ⟨.and, [7, 8]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [10, 3]⟩,
    ⟨.or, [11, 4]⟩, ⟨.and, [1, 12]⟩, ⟨.or, [9, 13]⟩], 14⟩

lemma monotoneWitness_size : monotoneWitness.size = 9 := rfl

lemma monotoneWitness_mono : Monotone2 monotoneWitness := by
  simp [Monotone2, monotoneWitness]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma monotoneWitness_eval : ∀ x : Fin 6 → Bool,
    monotoneWitness.eval (List.ofFn x) =
      Nat.testBit (4277075690 * 2 ^ 32 + 4277062856)
        (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

lemma monotoneWitness_upper (s : ℕ) (hs : 9 ≤ s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) =
        Nat.testBit (4277075690 * 2 ^ 32 + 4277062856)
          (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact ⟨monotoneWitness, monotoneWitness_mono, hs, monotoneWitness_eval⟩

end PEqualNP.Outside.L_meta_13154
