namespace PEqualNP.Outside.L_meta_2590.Petersen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma prime_is_edge (C : Circuit)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = pet x)
    (S : Finset (Fin 10)) (hs : IsPrimeImplicant 10 C S) :
    ∃ u v : Fin 10, graph.Adj u v ∧ S = {u,v} := by
  letI : DecidableRel graph.Adj := graphDec
  have ht : pet (setInput S) = true := (hf _).symm.trans hs.1
  rw [pet_graph,decide_eq_true_iff] at ht
  obtain ⟨u,v,huv,hu,hv⟩ := ht
  have huS : u ∈ S := by simpa [setInput] using hu
  have hvS : v ∈ S := by simpa [setInput] using hv
  have hsub : ({u,v} : Finset (Fin 10)) ⊆ S := by
    intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · exact huS
    · exact hvS
  refine ⟨u,v,huv,?_⟩
  by_contra hne
  have hproper : ({u,v} : Finset (Fin 10)) ⊂ S :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hsub,Ne.symm hne⟩
  have hfalse := hs.2 {u,v} (Finset.mem_ssubsets.mpr hproper)
  have htrue : pet (setInput ({u,v} : Finset (Fin 10))) = true := by
    rw [pet_graph,decide_eq_true_iff]
    exact ⟨u,v,huv,by simp [setInput],by simp [setInput]⟩
  have hcomp := hf (setInput ({u,v} : Finset (Fin 10)))
  change C.eval (List.ofFn (setInput ({u,v} : Finset (Fin 10)))) = false at hfalse
  rw [hfalse,htrue] at hcomp
  cases hcomp

lemma small_has_reread_edge (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 10 C)
    (hs : C.size ≤ 19) (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = pet x) :
    ∃ u v : Fin 10, graph.Adj u v ∧ readsAtMost C 10 (setList {u,v}) 1 = false := by
  classical
  have hn := small_not_read_one C hao hs hf
  change ¬ ∀ S, IsPrimeImplicant 10 C S → readsAtMost C 10 (setList S) 1 = true at hn
  push_neg at hn
  obtain ⟨S,hprime,hread⟩ := hn
  obtain ⟨u,v,huv,rfl⟩ := prime_is_edge C hf S hprime
  refine ⟨u,v,huv,?_⟩
  cases h : readsAtMost C 10 (setList {u,v}) 1
  · rfl
  · exact (hread h).elim

end PEqualNP.Outside.L_meta_2590.Petersen
