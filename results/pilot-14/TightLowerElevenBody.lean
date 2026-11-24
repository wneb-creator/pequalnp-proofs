namespace PEqualNP.Outside.L_meta_670_aux.TightFormula
open LiveCheck
lemma all_first_cases (i j : Fin 9) (u : Fin 4) : firstCase i j u = false := by
  fin_cases i
  · exact first0 j u
  · exact first1 j u
  · exact first2 j u
  · exact first3 j u
  · exact first4 j u
  · exact first5 j u
  · exact first6 j u
  · exact first7 j u
  · exact first8 j u

lemma high_nots_closed {t : Nat} (ht : 5 ≤ t) : Impossible 15 t raw :=
  high_nots_eleven all_first_cases ht

lemma binary_gates_lower {k t S} (h : Live k t S)
    (hs : ∀ a ∈ S, a ∈ LiteralBinary.literals) : t+11 ≤ k :=
  lower_eleven (from_cases all_first_cases) h hs
end PEqualNP.Outside.L_meta_670_aux.TightFormula
