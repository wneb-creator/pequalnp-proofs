import Mathlib
import PEqualNP.Defs

namespace PaschHardPiece
open PEqualNP.CircuitLowerBounds

def family : Fin 4 → Finset (Fin 6)
  | 0 => {0, 1, 2}
  | 1 => {0, 3, 4}
  | 2 => {1, 3, 5}
  | 3 => {2, 4, 5}

def gates : List Gate :=
  [⟨GateOp.and, [1, 4]⟩,
   ⟨GateOp.or, [0, 6]⟩,
   ⟨GateOp.or, [5, 6]⟩,
   ⟨GateOp.or, [7, 2]⟩,
   ⟨GateOp.or, [7, 3]⟩,
   ⟨GateOp.or, [8, 3]⟩,
   ⟨GateOp.or, [8, 2]⟩]

def output (i : Fin 4) : ℕ := 9 + i.val

def target (i : Fin 4) (x : Fin 6 → Bool) : Bool :=
  decide (∃ v ∈ family i, x v = true)

def value (i : Fin 4) (x : Fin 6 → Bool) : Bool :=
  Circuit.eval ⟨gates, output i⟩ (List.ofFn x)

def outside (i : Fin 4) : Fin 6 → Bool := fun v => decide (v ∉ family i)

def control (x : Fin 6 → Bool) : Bool :=
  (x 4 || x 0 || x 2) && (x 4 || x 5 || x 3) &&
  (x 1 || x 0 || x 3) && (x 1 || x 5 || x 2)

lemma control_mono : ∀ x y : Fin 6 → Bool,
    (∀ v, x v = true → y v = true) → control x = true → control y = true := by
  intro x y hxy
  simp only [control, Bool.and_eq_true, Bool.or_eq_true]
  aesop

lemma family_card : ∀ i, (family i).card = 3 := by decide

lemma linear : ∀ i j, i ≠ j → (family i ∩ family j).card ≤ 1 := by decide

lemma binary_monotone : ∀ g ∈ gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by simp [gates]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma low : ∀ i x, value i x = true → target i x = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
lemma conditional_correct : ∀ i x, control x = true → value i x = target i x := by decide

lemma control_at_outside : ∀ i, control (outside i) = true := by decide

lemma wrong_unconditional : ∃ i x, value i x ≠ target i x := by decide

lemma too_few_gates : gates.length < ∑ i : Fin 4, ((family i).card - 1) := by decide

end PaschHardPiece
