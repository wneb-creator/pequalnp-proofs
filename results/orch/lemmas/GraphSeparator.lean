import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

lemma false_on_some_edge_of_false_at_positive {n : ℕ}
    (E : List (Fin n × Fin n)) (h : (Fin n → Bool) → Bool) (mono : Monotone h)
    (x : Fin n → Bool) (positive : E.any (fun e => x e.1 && x e.2) = true)
    (negative : h x = false) :
    ∃ e ∈ E, h (fun i => decide (i = e.1 ∨ i = e.2)) = false := by
  obtain ⟨e, member, edge⟩ := List.any_eq_true.mp positive
  refine ⟨e, member, ?_⟩
  have bits : x e.1 = true ∧ x e.2 = true := by
    cases h1 : x e.1 <;> cases h2 : x e.2 <;> simp_all
  have small : (fun i => decide (i = e.1 ∨ i = e.2)) ≤ x := by
    intro i
    apply Bool.le_iff_imp.mpr
    intro hi
    rcases of_decide_eq_true hi with rfl | rfl
    · exact bits.1
    · exact bits.2
  have bound := mono small
  cases value : h (fun i => decide (i = e.1 ∨ i = e.2)) with
  | false => rfl
  | true =>
    have impossible : (true : Bool) ≤ false := by simpa only [value, negative] using bound
    exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) impossible)

end PEqualNP.Outside.L_meta_2592_aux
