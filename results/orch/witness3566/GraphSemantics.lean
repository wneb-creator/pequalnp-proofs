import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3566

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

theorem input_getD {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD]

theorem edgeList_graph_eval (n : ℕ) (es : List (ℕ × ℕ))
    (hvalid : ∀ e ∈ es, e.1 < n ∧ e.2 < n ∧ e.1 ≠ e.2) (x : Fin n → Bool) :
    graphFun (edgeGraph n es) ∅ x =
      es.any (fun e => (List.ofFn x).getD e.1 false && (List.ofFn x).getD e.2 false) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u, v, hAdj, hu, hv⟩
    rcases hAdj with ⟨_, hmem | hmem⟩
    · exact ⟨(u.val, v.val), hmem, (input_getD x u).trans hu, (input_getD x v).trans hv⟩
    · exact ⟨(v.val, u.val), hmem, (input_getD x v).trans hv, (input_getD x u).trans hu⟩
  · rintro ⟨⟨a, b⟩, he, ha, hb⟩
    have hh := hvalid (a, b) he
    let u : Fin n := ⟨a, hh.1⟩
    let v : Fin n := ⟨b, hh.2.1⟩
    refine ⟨u, v, ⟨?_, Or.inl he⟩, ?_, ?_⟩
    · intro h
      exact hh.2.2 (congrArg Fin.val h)
    · exact (input_getD x u).symm.trans ha
    · exact (input_getD x v).symm.trans hb

end PEqualNP.Outside.L_meta_3566
