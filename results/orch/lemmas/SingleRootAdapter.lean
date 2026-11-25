import FirstReject
namespace PEqualNP.Outside.L_meta_10760_first
lemma reject_one_cert {F : List Gt} {Q : List (Nat × Nat)} {fb : Nat × Nat}
    (hQ : ∀ e ∈ Q, Imp [] e.1 e.2) (hp : pOk 0 Q = true)
    (hfb : fbOk [] F fb = true) (hF : ∀ e ∈ F, Imp [e] 0 13)
    (hmin : Imp [] 0 13) (hcheck : okLs Q 13 fb [1] = true) :
    ∀ S : Finset Nat, (S : Set Nat) ⊆ C (mz 0) (WZ [] 0) →
      ¬ Live Z0 (mz 0) (tz 0) 13 1 S := by
  intro S hS hL
  have hc : chkT topC [] Q fb 0 13 [1] FF 1 = false := by
    simpa only [okLs, Bool.not_eq_true'] using hcheck
  refine reject_live topC_ok (K := 13) (F := F) (fb := fb)
    (by decide) (by decide) (by decide) hp hQ (Or.inr ⟨rfl, hfb⟩)
    (by simpa using hF) hmin hS hL (Or.inl rfl) [(FF, 1)] ffull ?_
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact chkT_chk hc 1 (by simp)
end PEqualNP.Outside.L_meta_10760_first
