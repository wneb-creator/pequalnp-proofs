import UnorderedFormulaTest
namespace PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
open LiveCheck TightFormula

lemma test_implies_one {n : Nat} {v : List Sig} : test n v = true → testOne n v = true := by
  induction n generalizing v with
  | zero => intro _; rfl
  | succ n ih =>
    intro h
    simp only [test, Bool.or_eq_true] at h
    simp only [testOne, Bool.or_eq_true]
    rcases h with h | h
    · exact Or.inl (Or.inl (Or.inl h))
    · obtain ⟨w, hw, hc⟩ := List.any_eq_true.mp h
      simp only [Bool.and_eq_true] at hc
      obtain ⟨hc, ht⟩ := hc
      exact Or.inl (Or.inr (List.any_eq_true.mpr
        ⟨w, hw, by simp only [hc, ih ht, Bool.true_and]⟩))

end PEqualNP.Outside.L_meta_670_aux.UnorderedFormula
