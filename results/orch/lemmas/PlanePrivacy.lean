import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Privacy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm

abbrev graph := PEqualNP.EdgeOwnership.edgeGraph 4 [(0,2),(0,3),(1,2)]

def circuit : Circuit :=
  { gates := [⟨.or,[0,1]⟩, ⟨.or,[0,2]⟩, ⟨.or,[2,3]⟩,
      ⟨.and,[4,5]⟩, ⟨.and,[5,6]⟩, ⟨.and,[7,8]⟩,
      ⟨.and,[4,2]⟩, ⟨.or,[9,10]⟩]
    output := 11 }

lemma no_four_cycle : NoFourCycle graph := by decide

lemma bipartite : ∀ u v : Fin 4, graph.Adj u v → decide (u.val < 2) ≠ decide (v.val < 2) := by
  decide

lemma strict : IsAO2 4 circuit := by decide

lemma computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = PEqualNP.MetaComplexity.NestedCover.graphFun graph ∅ x := by
  decide

lemma top_form : TopForm graph circuit := by decide

lemma lift_fixed : PEqualNP.Core.IsLiftFixedPoint graph circuit := by decide

lemma live : ∀ j < circuit.gates.length, PEqualNP.Core.InOutputCone 4 circuit j := by decide

lemma dirty : ¬ BelowF graph circuit 3 := by decide

lemma shared_or_operands :
    (NestedCover.gateAt circuit 3).inputs = [4,5] ∧
    (NestedCover.gateAt circuit 0).op = .or ∧
    (NestedCover.gateAt circuit 1).op = .or ∧
    4 ∈ (NestedCover.gateAt circuit 6).inputs ∧
    5 ∈ (NestedCover.gateAt circuit 4).inputs := by
  exact ⟨rfl,rfl,rfl,by decide,by decide⟩

lemma pair_prime : PEqualNP.ReadK.IsPrimeImplicant 4 circuit {0,3} := by decide

lemma pair_reread : PEqualNP.ReadK.readsAtMost circuit 4
    (PEqualNP.ReadK.setList ({0,3} : Finset (Fin 4))) 1 = false := by decide

lemma not_read_one : ¬ PEqualNP.ReadK.IsReadK 4 circuit 1 := by
  intro h
  have ht := h {0,3} pair_prime
  rw [pair_reread] at ht
  cases ht

end PEqualNP.Outside.L_meta_2583.Privacy
