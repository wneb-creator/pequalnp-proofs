import Mathlib.Data.Fintype.Fin

namespace PEqualNP.Outside.L_meta_2602_aux.Boundary

lemma bipartite_boundary_complete {n m : ℕ}
    (I : Fin n → Fin m → Prop) [DecidableRel I]
    (f : (Fin n → Bool) → (Fin m → Bool) → Bool)
    (mono : ∀ P L Q M, (∀ p, P p = true → Q p = true) →
      (∀ l, L l = true → M l = true) → f P L = true → f Q M = true)
    (positive : ∀ p l, I p l →
      f (fun q => decide (q = p)) (fun k => decide (k = l)) = true)
    (negative : ∀ P,
      f P (fun l => decide (∀ p, P p = true → ¬ I p l)) = false) :
    ∀ P L, f P L = true ↔ ∃ p l, I p l ∧ P p = true ∧ L l = true := by
  intro P L
  constructor
  · intro hPL
    by_contra bad
    let M := fun l => decide (∀ p, P p = true → ¬ I p l)
    have hLM (l) (hl : L l = true) : M l = true := by
      apply decide_eq_true
      intro p hp edge
      exact bad ⟨p,l,edge,hp,hl⟩
    have yes := mono P L P M (fun _ h => h) hLM hPL
    rw [negative P] at yes
    contradiction
  · rintro ⟨p,l,edge,hp,hl⟩
    apply mono (fun q => decide (q = p)) (fun k => decide (k = l)) P L
    · intro q hq
      have eq : q = p := of_decide_eq_true hq
      simpa only [eq] using hp
    · intro k hk
      have eq : k = l := of_decide_eq_true hk
      simpa only [eq] using hl
    · exact positive p l edge

end PEqualNP.Outside.L_meta_2602_aux.Boundary
