import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Bank

variable {p l : ℕ}

def basePoint (E : Finset (Fin p × Fin l)) (b : Fin l) (u : Fin p) : Bool :=
  decide ((u,b) ∉ E)

def raisedPoint (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l) (u : Fin p) : Bool :=
  decide (u = a ∨ (u,b) ∉ E)

lemma base_le_raised (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l)
    (u : Fin p) : basePoint E b u = true → raisedPoint E a b u = true := by
  simp only [basePoint,raisedPoint,decide_eq_true_eq]
  exact Or.inr

lemma point_bank_fixed (E : Finset (Fin p × Fin l))
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (a : Fin p) (b z : Fin l) (hab : (a,b)∈E)
    (S : Finset (Fin p)) (hS : 2 ≤ S.card)
    (hstar : ∀ u∈S, (u,z)∈E) (hres : a∈S → b≠z) :
    decide (∃ u∈S, basePoint E b u = true) =
      decide (∃ u∈S, raisedPoint E a b u = true) := by
  congr 1
  apply propext
  constructor
  · rintro ⟨u,hu,hv⟩
    exact ⟨u,hu,base_le_raised E a b u hv⟩
  · rintro ⟨u,hu,hv⟩
    rcases of_decide_eq_true hv with hua | hnot
    · subst u
      obtain ⟨v,hv,hva⟩ : ∃ v∈S, v≠a := by
        by_contra! hn
        have hsub : S ⊆ {a} := by intro v hv; simpa using hn v hv
        have hc := Finset.card_le_card hsub
        simp only [Finset.card_singleton] at hc
        omega
      have hnot : (v,b)∉E := by
        intro hvb
        exact h4 a v b z (Ne.symm hva) (hres hu) ⟨hab,hstar a hu,hvb,hstar v hv⟩
      exact ⟨v,hv,decide_eq_true hnot⟩
    · exact ⟨u,hu,decide_eq_true hnot⟩

lemma point_witness (E : Finset (Fin p × Fin l)) (a : Fin p) (b : Fin l)
    (hab : (a,b)∈E) :
    (¬ ∃ u v, (u,v)∈E ∧ basePoint E b u = true ∧ decide (v=b) = true) ∧
    (∃ u v, (u,v)∈E ∧ raisedPoint E a b u = true ∧ decide (v=b) = true) ∧
    (∀ u, u≠a → basePoint E b u = raisedPoint E a b u) := by
  refine ⟨?_,⟨a,b,hab,by simp [raisedPoint],by simp⟩,?_⟩
  · rintro ⟨u,v,hu,hpoint,hline⟩
    have hv : v=b := of_decide_eq_true hline
    subst v
    exact (of_decide_eq_true hpoint) hu
  · intro u hu
    simp [basePoint,raisedPoint,hu]

lemma all_point_banks_fixed (E : Finset (Fin p × Fin l))
    (h4 : ∀ a a' : Fin p, ∀ b b' : Fin l, a ≠ a' → b ≠ b' →
      ¬ ((a,b)∈E ∧ (a,b')∈E ∧ (a',b)∈E ∧ (a',b')∈E))
    (a : Fin p) (b : Fin l) (hab : (a,b)∈E)
    {ι : Type*} (S : ι → Finset (Fin p)) (z : ι → Fin l)
    (hS : ∀ i, 2 ≤ (S i).card)
    (hstar : ∀ i u, u∈S i → (u,z i)∈E)
    (hres : ∀ i, a∈S i → b≠z i) :
    ∀ i, decide (∃ u∈S i, basePoint E b u = true) =
      decide (∃ u∈S i, raisedPoint E a b u = true) := by
  intro i
  exact point_bank_fixed E h4 a b (z i) hab (S i) (hS i) (hstar i) (hres i)

end PEqualNP.Outside.L_meta_4675.Bank
