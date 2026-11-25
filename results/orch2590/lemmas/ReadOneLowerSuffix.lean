namespace PEqualNP.Outside.L_meta_2590.Petersen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma read_one_twenty (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 10 C)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = pet x)
    (hr : IsReadK 10 C 1) : 20 ≤ C.size := by
  letI : DecidableRel graph.Adj := graphDec
  have hcomp : ∀ x : Fin 10 → Bool, circuitFun 10 C x =
      decide (∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    exact (hf x).trans (pet_graph x)
  obtain ⟨T,hcover,hbound⟩ := ReadLower.General.main_aux 10 graph C no_four hao hcomp hr
  have hcard := cover_six T hcover
  rw [edge_count] at hbound
  omega

lemma small_not_read_one (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 10 C)
    (hs : C.size ≤ 19) (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = pet x) :
    ¬ IsReadK 10 C 1 := by
  intro hr
  have := read_one_twenty C hao hf hr
  omega

end PEqualNP.Outside.L_meta_2590.Petersen
