import FirstReject
namespace PEqualNP.Outside.L_meta_10760_first
lemma root13_of_shards {Q : List (Nat × Nat)} {M : List (Nat × Nat)}
    (hQ : ∀ e ∈ Q, Imp [] e.1 e.2) (hp : pOk 0 Q = true)
    (hM : mFull M = true)
    (hc : ∀ p ∈ M, chkT topC [] Q (1, 0) 0 12 (List.range 13) p.1 p.2 = false) :
    Imp [] 0 13 := by
  refine imp_FK topC_ok (F := []) (fb := (1, 0)) (K := 12)
    (by decide) (by decide) (Or.inl rfl) hp hQ (Or.inl rfl) (by simp) (Or.inr ?_)
  intro t ht
  exact ⟨M, hM, fun p hp => chkT_chk (hc p hp) t (List.mem_range.2 ht)⟩
lemma reject_one_shards {F : List Gt} {Q : List (Nat × Nat)}
    {fb : Nat × Nat} {M : List (Nat × Nat)}
    (hQ : ∀ e ∈ Q, Imp [] e.1 e.2) (hp : pOk 0 Q = true)
    (hfb : fbOk [] F fb = true) (hF : ∀ e ∈ F, Imp [e] 0 13)
    (hmin : Imp [] 0 13) (hM : mFull M = true)
    (hc : ∀ p ∈ M, chkT topC [] Q fb 0 13 [1] p.1 p.2 = false) :
    ∀ S : Finset Nat, (S : Set Nat) ⊆ C (mz 0) (WZ [] 0) →
      ¬ Live Z0 (mz 0) (tz 0) 13 1 S := by
  intro S hS hL
  refine reject_live topC_ok (K := 13) (F := F) (fb := fb)
    (by decide) (by decide) (by decide) hp hQ (Or.inr ⟨rfl, hfb⟩)
    (by simpa using hF) hmin hS hL (Or.inl rfl) M hM ?_
  intro p hp
  exact chkT_chk (hc p hp) 1 (by simp)
end PEqualNP.Outside.L_meta_10760_first
