import Mathlib

namespace PEqualNP.Outside.L_meta_4675.AnchoredBox

lemma internal_edge_on_anchor {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l)) (y : Fin p) (z : Fin l)
    (hA : ∀ a ∈ A, (a, z) ∈ E) (hB : ∀ b ∈ B, (y, b) ∈ E)
    (hyz : (y, z) ∈ E) {a : Fin p} {b : Fin l}
    (ha : a ∈ A) (hb : b ∈ B) (hab : (a, b) ∈ E) :
    a = y ∨ b = z := by
  by_contra hn
  push Not at hn
  exact h4 a y b z hn.1 hn.2 ⟨hab, hA a ha, hB b hb, hyz⟩

lemma residual_row_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (B : Finset (Fin l)) (y : Fin p) (hB : ∀ b ∈ B, (y, b) ∈ E)
    {a : Fin p} {b b' : Fin l} (hay : a ≠ y) (hb : b ∈ B) (hb' : b' ∈ B)
    (hab : (a, b) ∈ E) (hab' : (a, b') ∈ E) : b = b' := by
  by_contra hbb'
  exact h4 a y b b' hay hbb' ⟨hab, hab', hB b hb, hB b' hb'⟩

lemma residual_column_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (z : Fin l) (hA : ∀ a ∈ A, (a, z) ∈ E)
    {a a' : Fin p} {b : Fin l} (hbz : b ≠ z) (ha : a ∈ A) (ha' : a' ∈ A)
    (hab : (a, b) ∈ E) (ha'b : (a', b) ∈ E) : a = a' := by
  by_contra haa'
  exact h4 a a' b z haa' hbz ⟨hab, hA a ha, ha'b, hA a' ha'⟩

lemma residual_projection_cards {p l : ℕ} (E R : Finset (Fin p × Fin l))
    (h4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A : Finset (Fin p)) (B : Finset (Fin l)) (y : Fin p) (z : Fin l)
    (hA : ∀ a ∈ A, (a, z) ∈ E) (hB : ∀ b ∈ B, (y, b) ∈ E)
    (hR : ∀ e ∈ R, e ∈ E ∧ e.1 ∈ A ∧ e.2 ∈ B ∧ e.1 ≠ y ∧ e.2 ≠ z) :
    (R.image Prod.fst).card = R.card ∧ (R.image Prod.snd).card = R.card := by
  constructor
  · apply Finset.card_image_iff.mpr
    intro e he e' he' hf
    obtain ⟨heE, _, heB, hey, _⟩ := hR e he
    obtain ⟨he'E, _, he'B, _, _⟩ := hR e' he'
    apply Prod.ext hf
    apply residual_row_unique E h4 B y hB hey heB he'B heE
    simpa only [hf] using he'E
  · apply Finset.card_image_iff.mpr
    intro e he e' he' hs
    obtain ⟨heE, heA, _, _, hez⟩ := hR e he
    obtain ⟨he'E, he'A, _, _, _⟩ := hR e' he'
    apply Prod.ext ?_ hs
    apply residual_column_unique E h4 A z hA hez heA he'A heE
    simpa only [hs] using he'E

end PEqualNP.Outside.L_meta_4675.AnchoredBox
