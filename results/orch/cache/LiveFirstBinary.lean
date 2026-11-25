import FewNotBase

namespace PEqualNP.Outside.L_meta_2592.FewNot.Extended

lemma live_floor_from_pair_floor (base : List Sig) (target : Sig) (L : ℕ)
    (fresh : target ∉ base)
    (pairFloor : ∀ (d : ℕ) (a b : Sig), allowed true d → a ∈ base → b ∈ base →
      proper a → proper b → a ≠ b → ∀ (k : ℕ) (S : Finset Sig),
        Live true target k S → (∀ v ∈ S, v ∈ base ∨ v = bin d a b) → L ≤ k)
    {k : ℕ} {S : Finset Sig} (run : Live true target k S)
    (raw : ∀ v ∈ S, v ∈ base) : L + 1 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨rfl,hp⟩ := run
    exact False.elim (fresh (raw target (Finset.mem_singleton_self target)))
  | succ k =>
    obtain ⟨U,a,b,d,hd,rfl,hpa,hpb,hab,hfresh,tail⟩ := run
    have ha : a ∈ base := raw a (by simp)
    have hb : b ∈ base := raw b (by simp)
    have htail : ∀ v ∈ insert (bin d a b) U, v ∈ base ∨ v = bin d a b := by
      intro v hv
      rcases Finset.mem_insert.mp hv with hv | hv
      · exact Or.inr hv
      · exact Or.inl (raw v (by simp [hv]))
    have bound := pairFloor d a b hd ha hb hpa hpb hab k _ tail htail
    omega

end PEqualNP.Outside.L_meta_2592.FewNot.Extended
