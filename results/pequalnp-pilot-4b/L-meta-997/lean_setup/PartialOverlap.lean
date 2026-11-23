import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace Meta997PartialOverlap

def fixture : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.not, [6]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [8, 7]⟩,
  ⟨.and, [6, 9]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [12, 0]⟩], 13⟩

def y : Finset (Fin 6) := {0, 1}
def target : Fin 2 → Finset (Fin 6) := ![{0, 2, 3}, {4, 5}]
def output : Fin 2 → ℕ := ![13, 9]
def value (x : Fin 6 → Bool) (w : ℕ) : Bool :=
  (fixture.wires (List.ofFn x)).getD w false

theorem fanin_two_basis : ∀ g ∈ fixture.gates,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [fixture, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem output_correct : ∀ i : Fin 2, ∀ x : Fin 6 → Bool,
    value x (output i) = decide (∃ p ∈ target i, x p = true) := by decide

theorem targets_linear : ∀ i j : Fin 2, i ≠ j →
    (target i ∩ target j).card ≤ 1 := by decide

theorem only_one_not : ∀ i : Fin fixture.gates.length,
    (fixture.gates.get i).op = .not → (i : ℕ) = 1 := by
  intro i
  fin_cases i <;> simp [fixture]

theorem negation_true_below_y : ∀ x : Fin 6 → Bool,
    (Finset.univ.filter fun v => x v = true).card < y.card → value x 7 = true := by
  decide

theorem negation_false_at_y : value (fun v => decide (v ∈ y)) 7 = false := by decide

theorem switched_singleton_profile : ∀ p : Fin 6,
    value (fun v => decide (v = p)) 12 = true ↔ p ∈ ({2, 3} : Finset (Fin 6)) := by
  decide

theorem switched_background_profile : ∀ p : Fin 6, p ∉ y →
    (value (fun v => decide (v ∈ y ∨ v = p)) 12 = true ↔ p ∈ target 1) := by
  decide

theorem partial_light_support :
    ({2, 3} : Finset (Fin 6)) ⊂ target 0 ∧
    2 ≤ ({2, 3} : Finset (Fin 6)).card := by decide

theorem switched_not_a_refund :
    ¬ ((∃ i : Fin 2, ∀ p : Fin 6,
      value (fun v => decide (v = p)) 12 = true ↔ p ∈ target i) ∧
      (∃ i : Fin 2, Disjoint (target i) y ∧ ∀ p : Fin 6, p ∉ y →
        (value (fun v => decide (v ∈ y ∨ v = p)) 12 = true ↔ p ∈ target i))) := by
  decide

end Meta997PartialOverlap
