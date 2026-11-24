import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2584.CnfSix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

abbrev graph : SimpleGraph (Fin 6) := SimpleGraph.fromRel
  (fun u v => (u.val, v.val) ∈ [(0, 3), (0, 4), (1, 4), (1, 5), (2, 3), (2, 5)])

def circuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [0, 2]⟩,
    ⟨.or, [3, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 5]⟩,
    ⟨.or, [6, 2]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [7, 9]⟩,
    ⟨.or, [8, 10]⟩, ⟨.or, [6, 11]⟩, ⟨.and, [12, 13]⟩,
    ⟨.and, [17, 14]⟩, ⟨.and, [18, 15]⟩, ⟨.and, [19, 16]⟩], 20⟩

lemma size : circuit.size = 15 := rfl

lemma ao2 : PEqualNP.TopForm.IsAO2 6 circuit := by decide

lemma graph_four_free : PEqualNP.TopForm.NoFourCycle graph := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma computes : circuitFun 6 circuit = NestedCover.graphFun graph ∅ := by
  funext z
  revert z
  decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma top_form : PEqualNP.TopForm.TopForm graph circuit := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
lemma three_dirty : (PEqualNP.TopForm.junk graph circuit).card = 3 := by decide

lemma pair_prime : IsPrimeImplicant 6 circuit {0, 3} := by decide

lemma pair_joint_false : readsAtMost circuit 6 [0, 3] 2 = false := by decide

lemma pair_scalar_true : eachReadsAtMost circuit 6 [0, 3] 2 = true := by decide

lemma not_read_two : ¬ IsReadK 6 circuit 2 := by
  intro h
  have ht := h {0, 3} pair_prime
  have hs : setList ({0, 3} : Finset (Fin 6)) = [0, 3] := by decide
  rw [hs, pair_joint_false] at ht
  cases ht

end PEqualNP.Outside.L_meta_2584.CnfSix
