import KernelFirst13
namespace PEqualNP.Outside.L_meta_10760_first
lemma gate_bounds_sub {A B : List Gt} (hA : ∀ e ∈ A, Imp [e] 0 13)
    (hB : B.all (fun e => A.contains e) = true) : ∀ e ∈ B, Imp [e] 0 13 := by
  intro e he
  exact hA e (List.contains_iff_mem.1 (List.all_eq_true.1 hB e he))
lemma gate_bounds_nil : ∀ e ∈ ([] : List Gt), Imp [e] 0 13 := by simp
lemma gate_bounds_cons {e : Gt} {F : List Gt}
    (he : Imp [e] 0 13) (hF : ∀ f ∈ F, Imp [f] 0 13) : ∀ f ∈ e :: F, Imp [f] 0 13 := by
  intro f hf
  rcases List.mem_cons.1 hf with rfl | hf
  · exact he
  · exact hF f hf
lemma gate_bounds_append {A B : List Gt} (hA : ∀ e ∈ A, Imp [e] 0 13)
    (hB : ∀ e ∈ B, Imp [e] 0 13) : ∀ e ∈ A ++ B, Imp [e] 0 13 := by
  intro e he
  exact (List.mem_append.1 he).elim (hA e) (hB e)
end PEqualNP.Outside.L_meta_10760_first
