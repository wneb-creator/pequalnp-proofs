import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2585.CleanReadOne

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma clean_topform_read_one (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (htop : TopForm G C) (hJ : junk G C = ∅) :
    PEqualNP.ReadK.IsReadK n C 1 := by
  have hbelow := PEqualNP.Outside.L_meta_2585.CleanJunk.all_and_below_of_junk_empty n G C hJ
  apply PEqualNP.Outside.L_meta_2585_aux.Multilinear.syntactic_multilinear_read_one n C hAO
  apply PEqualNP.Outside.L_meta_2585_aux.Multilinear.no_nested_and_multilinear n C hAO
  · exact PEqualNP.Outside.L_meta_2585.CleanTopForm.no_nested_and n G C htop hbelow
  · exact PEqualNP.Outside.L_meta_2585.CleanTopForm.and_singleton_false n G C hbelow

lemma incidence_replacement_of_clean_topform (P L : ℕ)
    (I : Fin P → Fin L → Prop) [DecidableRel I] (C : Circuit)
    (G : SimpleGraph (Fin (P + L))) [DecidableRel G.Adj]
    (hAO : IsAO2 (P + L) C) (htop : TopForm G C) (hJ : junk G C = ∅)
    (hfun : ∀ z : Fin (P + L) → Bool,
      PEqualNP.MetaComplexity.circuitFun (P + L) C z =
        decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
          z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    ∃ D : Circuit, IsAO2 (P + L) D ∧
      (∀ z : Fin (P + L) → Bool,
        PEqualNP.MetaComplexity.circuitFun (P + L) D z =
          decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
            z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (P + L) D 1 := by
  exact ⟨C, hAO, hfun, le_rfl, clean_topform_read_one (P + L) G C hAO htop hJ⟩

end PEqualNP.Outside.L_meta_2585.CleanReadOne
