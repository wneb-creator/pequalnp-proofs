import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.TwoDirtyCycle

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def circuit : Circuit :=
  { gates := [
      ⟨.or, [0, 1]⟩,
      ⟨.or, [4, 5]⟩,
      ⟨.and, [6, 7]⟩,
      ⟨.or, [0, 2]⟩,
      ⟨.or, [3, 5]⟩,
      ⟨.and, [9, 10]⟩,
      ⟨.or, [8, 11]⟩,
      ⟨.or, [1, 2]⟩,
      ⟨.or, [13, 3]⟩,
      ⟨.and, [12, 14]⟩],
    output := 15 }

abbrev graph : SimpleGraph (Fin 6) :=
  edgeGraph 6 [(0, 3), (1, 4), (2, 5), (0, 4), (1, 5), (2, 3)]

theorem isAO2 : IsAO2 6 circuit := by decide

theorem below_cycle : ∀ x : Fin 6 → Bool, circuitFun 6 circuit x = true → graphFun graph ∅ x = true := by
  decide

theorem accepts_matching : ∀ i : Fin 3, circuitFun 6 circuit
    (pairInput (Fin.castAdd 3 i) (Fin.natAdd 3 i)) = true := by decide

theorem higher_prime : PEqualNP.ReadK.IsPrimeImplicant 6 circuit {0, 2, 4} := by decide

theorem no_four_cycle : NoFourCycle graph := by decide

theorem bipartite : ∀ u v : Fin 6, graph.Adj u v →
    decide (u.val < 3) ≠ decide (v.val < 3) := by decide

theorem two_dirty : junk graph circuit = {2, 5} := by decide

theorem common_dirty_pair : ¬ graph.Adj 0 5 ∧
    gateVal 6 circuit 2 (pairInput 0 5) = true ∧
    gateVal 6 circuit 5 (pairInput 0 5) = true ∧
    circuitFun 6 circuit (pairInput 0 5) = false := by decide

theorem not_read_one : ¬ PEqualNP.ReadK.IsReadK 6 circuit 1 := by
  intro h
  have hp : PEqualNP.ReadK.IsPrimeImplicant 6 circuit {0, 3} := by decide
  have hr := h {0, 3} hp
  have hf : PEqualNP.ReadK.readsAtMost circuit 6
      (PEqualNP.ReadK.setList ({0, 3} : Finset (Fin 6))) 1 = false := by decide
  rw [hf] at hr
  contradiction

theorem size_ten : circuit.size = 10 := rfl

def completed : Circuit :=
  { gates := circuit.gates ++ [⟨.and, [0, 4]⟩, ⟨.or, [15, 16]⟩], output := 17 }

theorem completed_ao2 : IsAO2 6 completed := by decide

theorem completed_computes : ∀ x : Fin 6 → Bool,
    circuitFun 6 completed x = graphFun graph ∅ x := by decide

theorem completed_two_dirty : junk graph completed = {2, 5} := by decide

theorem completed_not_read_one : ¬ PEqualNP.ReadK.IsReadK 6 completed 1 := by
  intro h
  have hp : PEqualNP.ReadK.IsPrimeImplicant 6 completed {0, 3} := by decide
  have hr := h {0, 3} hp
  have hf : PEqualNP.ReadK.readsAtMost completed 6
      (PEqualNP.ReadK.setList ({0, 3} : Finset (Fin 6))) 1 = false := by decide
  rw [hf] at hr
  contradiction

def stars : Circuit :=
  { gates := [⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩,
      ⟨.or, [4, 5]⟩, ⟨.and, [1, 8]⟩,
      ⟨.or, [3, 5]⟩, ⟨.and, [2, 10]⟩,
      ⟨.or, [7, 9]⟩, ⟨.or, [12, 11]⟩], output := 13 }

theorem stars_ao2 : IsAO2 6 stars := by decide

theorem stars_compute : ∀ x : Fin 6 → Bool,
    circuitFun 6 stars x = graphFun graph ∅ x := by decide

theorem stars_read_one : PEqualNP.ReadK.IsReadK 6 stars 1 := by decide

theorem sizes : stars.size = 8 ∧ circuit.size = 10 ∧ completed.size = 12 := by decide

end PEqualNP.Outside.L_meta_2583_aux.TwoDirtyCycle
