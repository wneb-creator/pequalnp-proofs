import KernelFirstEngine
namespace PEqualNP.Outside.L_meta_10760_first
lemma anyN_false_of_mem {h : Nat → Bool} {L : List Nat}
    (hh : ∀ t ∈ L, h t = false) : anyN h L = false := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change (Bool.rec (motive := fun _ => Bool) (anyN h L) true (h a) : Bool) = false
    rw [hh a (by simp)]
    exact ih (fun t ht => hh t (by simp [ht]))
lemma chkT_cover {top : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List W → Bool}
    {E : List Gt} {Q : List (Nat × Nat)} {fb : Nat × Nat} {Z K : Nat}
    {ts : List Nat} {tt : List (List Nat)} {H ph : Nat}
    (hcover : ∀ t ∈ ts, ∃ us ∈ tt, t ∈ us)
    (hchecks : ∀ us ∈ tt, chkT top E Q fb Z K us H ph = false) :
    chkT top E Q fb Z K ts H ph = false := by
  have hpoint : ∀ t ∈ ts, chkG top E Q fb Z K t H ph = false := by
    intro t ht
    obtain ⟨us, hus, htu⟩ := hcover t ht
    exact chkT_chk (hchecks us hus) t htu
  simp only [chkT, chkG, st_eq, pre_eq] at hpoint ⊢
  exact anyN_false_of_mem hpoint
end PEqualNP.Outside.L_meta_10760_first
