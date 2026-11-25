import KernelFirstTables
namespace PEqualNP.Outside.L_meta_10760_first
noncomputable def ownCheck (top : TopT) (e : Gt) (raw : List (Nat × Nat)) : List Nat → List ((Nat × Nat) × List Nat) → Bool
  | _, [] => true
  | own, r :: rs => okO top e own raw r && ownCheck top e raw (r.1.1 :: own) rs
lemma ownCheck_imp {top : TopT} (htop : TopOk top) {e : Gt}
    (he : e.2.1 < 7 ∧ e.2.2 < 7) {raw : List (Nat × Nat)}
    (hr : ∀ x ∈ raw, Imp [] x.1 x.2) {own : List Nat}
    (ho : ∀ x ∈ raw, x.1 ∈ own → Imp [e] x.1 x.2)
    {rs : List ((Nat × Nat) × List Nat)}
    (h : ownCheck top e raw own rs = true) :
    ∀ x ∈ raw, x.1 ∈ rs.map (fun r => r.1.1) ++ own → Imp [e] x.1 x.2 := by
  induction rs generalizing own with
  | nil => simpa using ho
  | cons r rs ih =>
    have hh : okO top e own raw r = true ∧ ownCheck top e raw (r.1.1 :: own) rs = true := by
      simpa only [ownCheck, Bool.and_eq_true] using h
    have hstep : ∀ x ∈ raw, x.1 ∈ r.1.1 :: own → Imp [e] x.1 x.2 :=
      ownAllP htop he hr ho (rs := [r]) (by simpa using hh.1)
    have htail := ih hstep hh.2
    intro x hx hc
    apply htail x hx
    simp only [List.map_cons, List.mem_append, List.mem_cons] at hc ⊢
    tauto
end PEqualNP.Outside.L_meta_10760_first
