import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.MethodObstruction

abbrev incidence (p l : Fin 2) : Prop := p = 0 ∨ l = 1

def cnfCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [0, 3]⟩,
    ⟨.and, [4, 5]⟩, ⟨.and, [7, 6]⟩], 8⟩

def starCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩,
    ⟨.or, [5, 6]⟩], 7⟩

lemma no_rectangle : ∀ p p' l l' : Fin 2, p ≠ p' → l ≠ l' →
    ¬(incidence p l ∧ incidence p l' ∧ incidence p' l ∧ incidence p' l') := by
  decide +kernel

lemma cnf_size : cnfCircuit.size = 5 := rfl

lemma cnf_ao : PEqualNP.TopForm.IsAO2 4 cnfCircuit := by
  decide +kernel

lemma cnf_correct : ∀ z : Fin (2 + 2) → Bool,
    PEqualNP.MetaComplexity.circuitFun (2 + 2) cnfCircuit z =
      decide (∃ p l : Fin 2, incidence p l ∧ z (Fin.castAdd 2 p) = true ∧
        z (Fin.natAdd 2 l) = true) := by
  decide +kernel

lemma edge_prime : PEqualNP.ReadK.IsPrimeImplicant 4 cnfCircuit {0, 2} := by
  decide +kernel

lemma edge_reread : PEqualNP.ReadK.readsAtMost cnfCircuit 4 [0, 2] 1 = false := by
  decide +kernel

lemma cnf_not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 cnfCircuit 1 := by
  intro h
  have hr := h {0, 2} edge_prime
  have hs : PEqualNP.ReadK.setList ({0, 2} : Finset (Fin 4)) = [0, 2] := by
    decide +kernel
  rw [hs, edge_reread] at hr
  contradiction

lemma point_linearization_loses_edge :
    PEqualNP.MetaComplexity.circuitFun 4 cnfCircuit
      (fun i => decide (i = 0 ∨ i = 2)) = true ∧
    PEqualNP.ReadK.lineSingle cnfCircuit 4 (fun w => decide (w < 2)) 0 2 = false := by
  decide +kernel

lemma star_size : starCircuit.size = 4 := rfl

lemma star_ao : PEqualNP.TopForm.IsAO2 4 starCircuit := by
  decide +kernel

lemma star_correct : ∀ z : Fin (2 + 2) → Bool,
    PEqualNP.MetaComplexity.circuitFun (2 + 2) starCircuit z =
      decide (∃ p l : Fin 2, incidence p l ∧ z (Fin.castAdd 2 p) = true ∧
        z (Fin.natAdd 2 l) = true) := by
  decide +kernel

lemma star_read_one : PEqualNP.ReadK.IsReadK 4 starCircuit 1 := by
  decide +kernel

end PEqualNP.Outside.L_meta_2583_aux.MethodObstruction
