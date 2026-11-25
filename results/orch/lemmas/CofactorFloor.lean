namespace PEqualNP.Outside.L_meta_2592.Signed

open PEqualNP.Outside.L_meta_5236
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation

lemma false_cofactor_floor_of_model {R : Type} (assign : R → Fin 10 → Bool)
    (roots : List (Wire R))
    (inputSupply : ∀ i : Fin 10, Available true roots (fun r => assign r i))
    (inputZero : ∀ r, assign r 0 = false)
    (floor : ∀ k bank, Reach true roots k bank →
      Available true bank (fun r => pet (assign r)) → 15 ≤ k)
    (v : Fin 10) (s : ℕ)
    (small : HasU2Size (fun x => pet (Function.update x v false)) s) : 15 ≤ s := by
  obtain ⟨D, _, size, computes⟩ := small
  let shift : R → Fin 10 → Bool := fun r => assign r ∘ vertexInv v
  have zero : ∀ r, shift r v = false := by
    intro r
    exact (congrArg (assign r) (vertexInv_zero v)).trans (inputZero r)
  have supplied : ∀ i : Fin 10, Available true roots (fun r => shift r i) := by
    intro i
    exact inputSupply (vertexInv v i)
  obtain ⟨bank, history, output⟩ := reach_u2 shift roots supplied D
  have eqOutput : (fun r => u2Eval D (shift r)) = (fun r => pet (assign r)) := by
    funext r
    rw [computes]
    change pet (Function.update (shift r) v false) = pet (assign r)
    have fixed : Function.update (shift r) v false = shift r := by
      funext i
      by_cases hi : i = v
      · subst i
        simp [zero]
      · exact Function.update_of_ne hi false (shift r)
    rw [fixed]
    exact pet_vertexInv v (assign r)
  rw [eqOutput] at output
  exact (floor _ _ history output).trans size

end PEqualNP.Outside.L_meta_2592.Signed
