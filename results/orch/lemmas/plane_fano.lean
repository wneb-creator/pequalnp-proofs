import PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583.Fano

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

abbrev incidence (p l : Fin 7) : Prop :=
  (p.val + 7 - l.val) % 7 = 0 ∨ (p.val + 7 - l.val) % 7 = 1 ∨
    (p.val + 7 - l.val) % 7 = 3

lemma line_card : ∀ l : Fin 7, (Finset.univ.filter (fun p => incidence p l)).card = 3 := by
  decide

lemma unique_join : ∀ p p' : Fin 7, p ≠ p' → ∃! l : Fin 7, incidence p l ∧ incidence p' l := by
  simp only [ExistsUnique]
  decide

def target (z : Fin (7 + 7) → Bool) : Bool :=
  decide (∃ p l : Fin 7, incidence p l ∧ z (Fin.castAdd 7 p) = true ∧
    z (Fin.natAdd 7 l) = true)

lemma read_lower (C : Circuit) (hAO : PEqualNP.TopForm.IsAO2 (7 + 7) C)
    (hfun : ∀ z : Fin (7 + 7) → Bool, circuitFun (7 + 7) C z = target z)
    (hread : IsReadK (7 + 7) C 1) : 27 ≤ C.size := by
  exact ReadLower.fano_bound incidence C line_card unique_join hAO hfun hread

lemma read_upper : ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (7 + 7) D ∧
    (∀ z : Fin (7 + 7) → Bool, circuitFun (7 + 7) D z = target z) ∧
    IsReadK (7 + 7) D 1 ∧ D.size = 27 := by
  obtain ⟨D, hAO, hfun, hread, hsize⟩ := PlaneUpper.upper 2 7 incidence (by decide) line_card
  exact ⟨D, hAO, hfun, hread, by omega⟩

lemma small_circuit_obstructs_replacement (C : Circuit) (hsize : C.size ≤ 26) :
    ¬ ∃ D : Circuit, PEqualNP.TopForm.IsAO2 (7 + 7) D ∧
      (∀ z : Fin (7 + 7) → Bool, circuitFun (7 + 7) D z = target z) ∧
      D.size ≤ C.size ∧ IsReadK (7 + 7) D 1 := by
  rintro ⟨D, hAO, hfun, hle, hread⟩
  have h := read_lower D hAO hfun hread
  omega

end PEqualNP.Outside.L_meta_2583.Fano
