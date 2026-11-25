import Mathlib.Order.Monotone.Defs
import Mathlib.Data.Bool.Basic

namespace PEqualNP.Outside.L_meta_2592.OneNot

lemma replace_true {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!h x) = f x)
    (below : ∀ x, h x ≤ f x) :
    ∀ x, G x true = f x := by
  intro x
  have hm := mono x
  have hc := correct x
  have hb := below x
  cases hh : h x <;> cases hf : f x <;>
    cases h0 : G x false <;> cases h1 : G x true <;> simp_all [Bool.le_iff_imp]

lemma replace_false {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!h x) = f x)
    (above : ∀ x, f x ≤ h x) :
    ∀ x, G x false = f x := by
  intro x
  have hm := mono x
  have hc := correct x
  have ha := above x
  cases hh : h x <;> cases hf : f x <;>
    cases h0 : G x false <;> cases h1 : G x true <;> simp_all [Bool.le_iff_imp]

lemma essential_witnesses {α : Type*} (f h : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, G x false ≤ G x true)
    (correct : ∀ x, G x (!h x) = f x)
    (essentialFalse : ∃ x, G x false ≠ f x)
    (essentialTrue : ∃ x, G x true ≠ f x) :
    (∃ x, h x = false ∧ f x = true) ∧
      (∃ x, h x = true ∧ f x = false) := by
  obtain ⟨a, ha⟩ := essentialFalse
  obtain ⟨b, hb⟩ := essentialTrue
  constructor
  · refine ⟨a, ?_⟩
    have hm := mono a
    have hc := correct a
    cases hh : h a <;> cases hf : f a <;>
      cases h0 : G a false <;> cases h1 : G a true <;> simp_all [Bool.le_iff_imp]
  · refine ⟨b, ?_⟩
    have hm := mono b
    have hc := correct b
    cases hh : h b <;> cases hf : f b <;>
      cases h0 : G b false <;> cases h1 : G b true <;> simp_all [Bool.le_iff_imp]

end PEqualNP.Outside.L_meta_2592.OneNot
