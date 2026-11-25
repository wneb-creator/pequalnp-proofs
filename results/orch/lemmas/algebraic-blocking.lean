import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1479

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
lemma fano_blocking_iff_contains_line : ∀ s : Finset (Fin 7),
    (∀ l : Fin 7, ∃ p ∈ s, p = l ∨ p = l + 1 ∨ p = l + 3) ↔
      ∃ l : Fin 7, ∀ p : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → p ∈ s := by
  decide

lemma fano_mask_pure_points_contains_line
    (g : (Fin 14 → Bool) → Bool) (mono : Monotone g)
    (correct : ∀ x : Fin 14 → Bool,
      (g x = true ∧ ∃ l : Fin 7, x (Fin.natAdd 7 l) = true) ↔
        ∃ p l : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) ∧
          x (Fin.castAdd 7 p) = true ∧ x (Fin.natAdd 7 l) = true)
    (s : Finset (Fin 7))
    (on : g (fun i => Fin.addCases (fun p : Fin 7 => decide (p ∈ s))
      (fun _ : Fin 7 => false) i) = true) :
    ∃ l : Fin 7, ∀ p : Fin 7, (p = l ∨ p = l + 1 ∨ p = l + 3) → p ∈ s := by
  apply (fano_blocking_iff_contains_line s).mp
  intro l
  let base : Fin 14 → Bool := fun i => Fin.addCases (fun p : Fin 7 => decide (p ∈ s))
    (fun _ : Fin 7 => false) i
  let next : Fin 14 → Bool := fun i => Fin.addCases (fun p : Fin 7 => decide (p ∈ s))
    (fun t : Fin 7 => decide (t = l)) i
  have below : base ≤ next := by
    intro i
    refine Fin.addCases (m := 7) (n := 7) (fun p => ?_) (fun t => ?_) i
    · simp only [base,next,Fin.addCases_left,le_refl]
    · simp only [base,next,Fin.addCases_right,Bool.false_le]
  have hon : g next = true := by
    have h := mono below
    change g base ≤ g next at h
    rw [show g base = true from on] at h
    exact Bool.eq_true_of_true_le h
  obtain ⟨p,t,inc,hp,ht⟩ := (correct next).mp
    ⟨hon,l,by simp only [next,Fin.addCases_right,decide_true]⟩
  have ht' : t = l := by simpa only [next,Fin.addCases_right,decide_eq_true_eq] using ht
  subst t
  exact ⟨p,by simpa only [next,Fin.addCases_left,decide_eq_true_eq] using hp,inc⟩

end PEqualNP.Outside.L_meta_1479
