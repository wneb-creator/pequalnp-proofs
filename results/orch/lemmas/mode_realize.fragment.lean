namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma realizeBankMode (u : Bool) (C : Circuit) (w : List Sig)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (mono : u = false → ∀ g ∈ C.gates, isNot g = false)
    (plain : w.all plainWord = true)
    (computes : ∀ r : Row, C.eval (w.map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u target k S ∧
      ∀ a ∈ S, a ∈ w := by
  have he : (execute C.gates w).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [←b_read,execute_bits _ _ _ (fun g hg => (legal g hg).1)]
    exact computes r
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u:=u) (execute C.gates w) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target=false by decide +kernel)] at out
  obtain ⟨k,S,hk,run,hs⟩ := extract C.gates w legal (u:=u) mono hp
    (out.resolve_right (fun h => h hp))
  rw [nrm_map plain] at hs
  exact ⟨k,S,hk,run,hs⟩

lemma realizeMonotoneBank (C : Circuit) (w : List Sig)
    (mono : Monotone2 C) (plain : w.all plainWord = true)
    (computes : ∀ r : Row, C.eval (w.map (bit r)) = bit r target) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ w := by
  have legal : FanInTwo C := by
    intro g hg
    obtain ⟨hop,arity⟩ := mono g hg
    refine ⟨?_,arity⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop ⊢
    exact hop.elim Or.inl (Or.inr ∘ Or.inl)
  have noNot : false = false → ∀ g ∈ C.gates, isNot g = false := by
    intro _ g hg
    have hop := (mono g hg).1
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hop
    rcases hop with h | h <;> simp [isNot,h]
  obtain ⟨k,S,hk,run,raw⟩ := realizeBankMode false C w legal noNot plain computes
  exact ⟨k,S,hk.trans List.countP_le_length,run,raw⟩

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
