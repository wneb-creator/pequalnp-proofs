import Mathlib

namespace PEqualNP.Outside.L_meta_2592_aux.NotComparison

lemma replace_true_of_le {α : Type*} (f h : α → Bool) (q : α → Bool → Bool)
    (qmono : ∀ x, q x false ≤ q x true)
    (correct : ∀ x, q x (!h x) = f x)
    (hbelow : ∀ x, h x ≤ f x) :
    ∀ x, q x true = f x := by
  intro x
  have hm := qmono x
  have hc := correct x
  have hb := hbelow x
  cases hh : h x <;> cases hf : f x <;> simp_all

lemma replace_false_of_le {α : Type*} (f h : α → Bool) (q : α → Bool → Bool)
    (qmono : ∀ x, q x false ≤ q x true)
    (correct : ∀ x, q x (!h x) = f x)
    (fbelow : ∀ x, f x ≤ h x) :
    ∀ x, q x false = f x := by
  intro x
  have hm := qmono x
  have hc := correct x
  have hb := fbelow x
  cases hh : h x <;> cases hf : f x <;> simp_all

lemma essential_not_incomparable {α : Type*} (f h : α → Bool) (q : α → Bool → Bool)
    (qmono : ∀ x, q x false ≤ q x true)
    (correct : ∀ x, q x (!h x) = f x)
    (true_fails : ¬ ∀ x, q x true = f x)
    (false_fails : ¬ ∀ x, q x false = f x) :
    (∃ x, h x = true ∧ f x = false) ∧ (∃ x, h x = false ∧ f x = true) := by
  have hn : ¬ ∀ x, h x ≤ f x := fun le =>
    true_fails (replace_true_of_le f h q qmono correct le)
  have fn : ¬ ∀ x, f x ≤ h x := fun le =>
    false_fails (replace_false_of_le f h q qmono correct le)
  push_neg at hn fn
  obtain ⟨x, hx⟩ := hn
  obtain ⟨y, hy⟩ := fn
  constructor
  · refine ⟨x, ?_⟩
    cases hh : h x <;> cases hf : f x <;> simp_all
  · refine ⟨y, ?_⟩
    cases hh : h y <;> cases hf : f y <;> simp_all

end PEqualNP.Outside.L_meta_2592_aux.NotComparison
