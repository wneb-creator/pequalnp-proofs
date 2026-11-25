import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def f (x : Fin 7 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def CC : List Gate := [
  ⟨.and, [0, 2]⟩,
  ⟨.and, [1, 4]⟩,
  ⟨.or, [0, 3]⟩,
  ⟨.and, [5, 9]⟩,
  ⟨.or, [0, 2]⟩,
  ⟨.or, [4, 6]⟩,
  ⟨.and, [11, 12]⟩,
  ⟨.or, [3, 5]⟩,
  ⟨.or, [1, 6]⟩,
  ⟨.and, [14, 15]⟩,
  ⟨.or, [7, 8]⟩,
  ⟨.or, [10, 13]⟩,
  ⟨.or, [17, 18]⟩,
  ⟨.or, [19, 16]⟩]

set_option maxRecDepth 100000 in
lemma dec_f : ∀ x : Fin 7 → Bool, decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true) = f x := by decide +kernel

set_option maxRecDepth 100000 in
lemma CC_f : ∀ x : Fin 7 → Bool, Circuit.eval ⟨CC, 20⟩ (List.ofFn x) = f x := by decide +kernel

lemma CC_monotone : ∀ g ∈ CC, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [CC]

lemma CC_length : CC.length = 14 := rfl

end PEqualNP.Outside.L_meta_10760
