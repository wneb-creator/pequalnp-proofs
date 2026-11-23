import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace FanoUpperAudit

def lines : Fin 7 → Finset (Fin 7) :=
  ![{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}]

def gates : List Gate :=
  [⟨.or, [0, 1]⟩, ⟨.or, [0, 3]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [2, 3]⟩,
   ⟨.or, [1, 4]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [0, 5]⟩, ⟨.or, [2, 7]⟩,
   ⟨.or, [4, 8]⟩, ⟨.or, [5, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.or, [6, 11]⟩,
   ⟨.or, [5, 12]⟩, ⟨.or, [6, 13]⟩]

def out : Fin 7 → ℕ := ![14, 15, 20, 16, 18, 17, 19]

example : (∀ i, (lines i).card = 3) ∧
    (∀ i j, i ≠ j → (lines i ∩ lines j).card = 1) ∧
    (∀ p, (Finset.univ.filter (fun i => p ∈ lines i)).card = 3) := by decide

example : gates.length = 14 := by decide

example : ∀ g ∈ gates, g.op = .or ∧ g.inputs.length = 2 := by simp [gates]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
example : ∀ (w : Fin 7) (x : Fin 7 → Bool),
    Circuit.eval ⟨gates, out w⟩ (List.ofFn x) =
      decide (∃ v ∈ lines w, x v = true) := by decide

end FanoUpperAudit
