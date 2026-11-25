import PEqualNP.Outside.L_meta_7493

namespace PEqualNP.Outside.L_meta_2592_aux.FirstBinary

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_7493
open CircuitProof CircuitProof.Readers

lemma least_no_constant {n : ℕ} {f : (Fin n → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (L : Least n f gs o) (hnc : ∃ x y, f x ≠ f y)
    (p : ℕ) (hp : p < gs.length) (c : Bool) :
    ¬ ∀ x : Fin n → Bool, vl gs x (n + p) = c := by
  intro constant
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], by simp [hp]⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  obtain ⟨gs', o', hcl, shorter, cost, evaluates⟩ :=
    drop_core n pre g post L.hcl o (Sum.inl c)
      (fun x => ⟨trivial, (constant x).symm⟩) (L.ncv hnc)
  have budget : nonNotCount gs' ≤ nonNotCount (pre ++ g :: post) := by
    simp only [nonNotCount, List.countP_append, List.countP_cons] at cost ⊢
    omega
  have minimal := L.hmin gs' o' hcl (fun x => (evaluates x).trans (L.hev x)) budget
  omega

end PEqualNP.Outside.L_meta_2592_aux.FirstBinary
