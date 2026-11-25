import OwnRows
namespace PEqualNP.Outside.L_meta_10760_first
lemma ty_imp_shards {gs : List Gt} {raw : List (Nat × Nat)} {i : Nat} {e : Gt}
    {own cs : List Nat} {fb : Nat × Nat} {M : List (Nat × Nat)}
    (hr : ∀ x ∈ raw, Imp [] x.1 x.2)
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2)
    (hshape : okTy gs raw 12 i e own cs fb [List.range 13] = true)
    (hM : mFull M = true)
    (hchecks : ∀ p ∈ M, chkT topC [e] (tabE e own (pick raw cs)) fb 0 12 (List.range 13) p.1 p.2 = false)
    (h0 : Imp [] 0 13) (hF : ∀ f ∈ gs.take i, Imp [f] 0 13) : Imp [e] 0 13 := by
  simp only [okTy, Bool.and_eq_true] at hshape
  obtain ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩ := hshape
  refine imp_FK topC_ok (K := 12) (by decide) (by decide)
    (Or.inr ⟨e, rfl, Nat.le_of_ble_eq_true a1, Nat.le_of_ble_eq_true a2, h0⟩)
    a4 (rootQ hr ho) (Or.inr ⟨rfl, a5⟩) ?_ (Or.inr ?_)
  · simpa using hF
  · intro t ht
    exact ⟨M, hM, fun p hp => chkT_chk (hchecks p hp) t (List.mem_range.2 ht)⟩
end PEqualNP.Outside.L_meta_10760_first
