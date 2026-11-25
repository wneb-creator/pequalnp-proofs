import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.SemanticMinterms

def edgeFun {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin (p + l) → Bool) : Bool :=
  decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
    x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)

lemma eq_edgeFun_of_pair_checks {p l : ℕ} (E : Finset (Fin p × Fin l))
    (g : (Fin (p + l) → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → g x = true → g y = true)
    (hle : ∀ x, g x = true → edgeFun E x = true)
    (hpairs : ∀ a b, (a, b) ∈ E →
      g (fun i => decide (i = Fin.castAdd l a ∨ i = Fin.natAdd p b)) = true) :
    ∀ x, g x = edgeFun E x := by
  intro x
  cases hx : edgeFun E x with
  | false =>
    cases hg : g x with
    | false => rfl
    | true =>
      have hbad := hle x hg
      simp only [hx, Bool.false_eq_true] at hbad
  | true =>
    obtain ⟨a, b, hab, hxa, hxb⟩ := of_decide_eq_true hx
    apply hmono _ x _ (hpairs a b hab)
    intro i hi
    rcases of_decide_eq_true hi with hi | hi
    · simpa only [hi] using hxa
    · simpa only [hi] using hxb

end PEqualNP.Outside.L_meta_4675.SemanticMinterms
