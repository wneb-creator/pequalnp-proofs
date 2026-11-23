import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_997.PartialOverlap
open PEqualNP.CircuitLowerBounds

def C : Circuit := ⟨[
  ⟨.and, [0, 1]⟩,
  ⟨.not, [7]⟩,
  ⟨.or, [2, 3]⟩,
  ⟨.or, [4, 5]⟩,
  ⟨.and, [8, 9]⟩,
  ⟨.and, [7, 10]⟩,
  ⟨.or, [11, 12]⟩,
  ⟨.or, [0, 13]⟩,
  ⟨.or, [10, 6]⟩], 14⟩
def S : Fin 2 → Finset (Fin 7) := ![{0, 2, 3}, {4, 5, 6}]
def Y : Finset (Fin 7) := {0, 1}
def O : Fin 2 → ℕ := ![14, 15]
def value (x : Fin 7 → Bool) (w : ℕ) := (C.wires (List.ofFn x)).getD w false

theorem pairwise_intersection : ∀ i j : Fin 2, i ≠ j → (S i ∩ S j).card ≤ 1 := by decide

theorem permitted_gates : ∀ g ∈ C.gates,
    (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by simp [C]

theorem unique_not : ∀ i : Fin C.gates.length, (C.gates.get i).op = .not → (i : ℕ) = 1 := by
  intro i
  fin_cases i <;> simp [C]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem exact_outputs : ∀ (i : Fin 2) (x : Fin 7 → Bool),
    value x (O i) = decide (∃ p ∈ S i, x p = true) := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem light_window : ∀ x : Fin 7 → Bool,
    (Finset.univ.filter (fun v => x v = true)).card < Y.card → value x 8 = true := by decide

theorem heavy_window : value (fun v => decide (v ∈ Y)) 8 = false := by decide

def lightSupport : Finset (Fin 7) := Finset.univ.filter (fun p =>
  value (fun v => decide (v = p)) 13 = true)
def heavySupport : Finset (Fin 7) := Finset.univ.filter (fun p =>
  p ∉ Y ∧ value (fun v => decide (v ∈ Y ∨ v = p)) 13 = true)

theorem light_partial : lightSupport = {2, 3} := by decide
theorem heavy_partial : heavySupport = {4, 5} := by decide

theorem both_coarse_charges : lightSupport ⊆ S 0 ∧ 2 ≤ lightSupport.card ∧
    Disjoint (S 1) Y ∧ heavySupport ⊆ S 1 ∧ 2 ≤ heavySupport.card := by decide

theorem no_exact_light_profile : ¬ ∃ i : Fin 2, ∀ p : Fin 7,
    value (fun v => decide (v = p)) 13 = true ↔ p ∈ S i := by decide

theorem no_exact_heavy_profile : ¬ ∃ i : Fin 2, Disjoint (S i) Y ∧ ∀ p : Fin 7,
    p ∉ Y → (value (fun v => decide (v ∈ Y ∨ v = p)) 13 = true ↔ p ∈ S i) := by decide

end PEqualNP.Outside.L_meta_997.PartialOverlap
