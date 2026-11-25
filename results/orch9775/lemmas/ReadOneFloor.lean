import GraphFacts
import PEqualNP.Outside.L_meta_2237

namespace PEqualNP.Outside.L_meta_9775.ReadOneFloor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHarness GraphFacts

theorem twenty_five (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x)
    (hr : PEqualNP.ReadK.IsReadK 14 C 1) : 25 ≤ C.size := by
  have hf : ∀ x : Fin 14 → Bool, circuitFun 14 C x =
      decide (∃ u v : Fin 14, graph.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    exact (hc x).trans (target_graph x)
  obtain ⟨T, hT, hsize⟩ := PEqualNP.Outside.L_meta_2237
    14 graph C no_four_cycle hAO hf hr
  have hcover := cover_size T hT
  rw [edge_card] at hsize
  omega

theorem no_read_one_candidate (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x)
    (hs : C.size ≤ 24) : ¬ PEqualNP.ReadK.IsReadK 14 C 1 := by
  intro hr
  have := twenty_five C hAO hc hr
  omega

end PEqualNP.Outside.L_meta_9775.ReadOneFloor
