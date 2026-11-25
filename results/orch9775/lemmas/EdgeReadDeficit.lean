import ReadOneFloor

namespace PEqualNP.Outside.L_meta_9775.EdgeReadDeficit

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity CircuitHarness

lemma edge_order : ∀ u v : Fin 14, (u, v) ∈ edges → u < v := by decide

lemma all_edge_reads (C : Circuit)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x)
    (he : ∀ u v : Fin 14, (u, v) ∈ edges →
      PEqualNP.ReadK.readsAtMost C 14 [u.val, v.val] 1 = true) :
    PEqualNP.ReadK.IsReadK 14 C 1 := by
  intro S hS
  have ha : target (PEqualNP.ReadK.setInput S) = true := by
    rw [← hc]
    exact hS.1
  obtain ⟨u, v, huv, hu, hv⟩ := (target_spec _).mp ha
  have heuv : (u, v) ∈ edges := (edge_iff u v).mpr huv
  have huS : u ∈ S := by simpa [PEqualNP.ReadK.setInput] using hu
  have hvS : v ∈ S := by simpa [PEqualNP.ReadK.setInput] using hv
  have hsub : ({u, v} : Finset (Fin 14)) ⊆ S := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact huS
    · exact (Finset.mem_singleton.mp hw) ▸ hvS
  have hp : circuitFun 14 C (PEqualNP.ReadK.setInput {u, v}) = true := by
    change C.eval (List.ofFn _) = true
    rw [hc]
    apply (target_spec _).mpr
    exact ⟨u, v, huv, by simp [PEqualNP.ReadK.setInput],
      by simp [PEqualNP.ReadK.setInput]⟩
  have hEq : ({u, v} : Finset (Fin 14)) = S := by
    by_contra hn
    have hproper : ({u, v} : Finset (Fin 14)) ⊂ S := by
      exact Finset.ssubset_def.mpr ⟨hsub, fun hr => hn (Finset.Subset.antisymm hsub hr)⟩
    have hf := hS.2 {u, v} (Finset.mem_ssubsets.mpr hproper)
    exact Bool.noConfusion (hp.symm.trans hf)
  rw [← hEq, PEqualNP.Outside.L_meta_2237.cor_setList_pair u v (edge_order u v heuv)]
  exact he u v heuv

theorem deficient_edge (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 14 C)
    (hc : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = target x)
    (hs : C.size ≤ 24) :
    ∃ u v : Fin 14, (u, v) ∈ edges ∧
      PEqualNP.ReadK.readsAtMost C 14 [u.val, v.val] 1 = false := by
  by_contra hn
  apply ReadOneFloor.no_read_one_candidate C hAO hc hs
  apply all_edge_reads C hc
  intro u v he
  cases h : PEqualNP.ReadK.readsAtMost C 14 [u.val, v.val] 1
  · exact False.elim (hn ⟨u, v, he, h⟩)
  · rfl

end PEqualNP.Outside.L_meta_9775.EdgeReadDeficit
