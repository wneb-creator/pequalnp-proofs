import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.PG3

abbrev incidence (p l : Fin 13) : Prop :=
  Nat.testBit (([1170, 113, 2584, 4372, 15, 4674, 2338, 7169, 1352, 1572, 897, 2244, 4264] : List Nat).getD p.val 0) l.val = true

set_option maxHeartbeats 1000000 in
lemma lineSize : ∀ l : Fin 13,
    (Finset.univ.filter (fun p => incidence p l)).card = 4 := by
  decide

set_option maxHeartbeats 1000000 in
lemma pairLine : ∀ p p' : Fin 13, p ≠ p' →
    ∃! l : Fin 13, incidence p l ∧ incidence p' l := by
  change ∀ p p' : Fin 13, p ≠ p' →
    ∃ l : Fin 13, (incidence p l ∧ incidence p' l) ∧
      ∀ l' : Fin 13, (incidence p l' ∧ incidence p' l') → l' = l
  decide

abbrev matchedLine : Fin 13 → Fin 13 :=
  ![10, 5, 4, 2, 0, 12, 1, 11, 8, 9, 7, 6, 3]

lemma matchingIncident : ∀ p : Fin 13, incidence p (matchedLine p) := by
  decide

lemma matchingInjective : Function.Injective matchedLine := by
  decide

end PEqualNP.Outside.L_meta_2583_aux.PG3
