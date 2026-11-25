namespace PEqualNP.Outside.L_meta_2590.MonoNine
open PEqualNP.CircuitLowerBounds
lemma monotone_roots (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) :
    ∃ k, k ≤ C.size ∧ Live false graph k inputs.toFinset := by
  have legal : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    have h := hm g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
    exact ⟨h.1.imp id Or.inl, h.2⟩
  have mono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    rcases (hm g hg).1 with h | h
    · simp [isNot, h]
    · simp only [Set.mem_singleton_iff] at h
      simp [isNot, h]
  have goalEq : (execute C.gates inputs).getD C.output zero = graph:=by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (u:=false) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph=false:=by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=false) C.gates inputs legal (fun _ => mono) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord=true:=by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a:=by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset:=by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k, hk.trans List.countP_le_length, eq ▸ run⟩
lemma monotone_sixteen (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 9 → Bool, PEqualNP.MetaComplexity.circuitFun 9 C x = edge x) :
    16 ≤ C.size := by
  obtain ⟨k, hk, hrun⟩ := monotone_roots C hm (funext computes)
  by_contra h
  exact monoRoot k (by omega) hrun
end PEqualNP.Outside.L_meta_2590.MonoNine
