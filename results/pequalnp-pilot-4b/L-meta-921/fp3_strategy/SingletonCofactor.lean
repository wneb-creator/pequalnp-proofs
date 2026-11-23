import Mathlib

namespace PEqualNP.Outside.Meta921Strategy

variable {α : Type*} [DecidableEq α]

def MonotoneCut (F : Finset α → Bool → Bool) : Prop :=
  ∀ X Y z w, X ⊆ Y → (z = true → w = true) →
    F X z = true → F Y w = true

def OrCut (a b : α) (X : Finset α) : Bool := decide (a ∈ X ∨ b ∈ X)

theorem singleton_cut_upper_correct
    (F : Finset α → Bool → Bool) (a b : α) (L : Finset α) (k : ℕ)
    (hab : a ≠ b) (hmono : MonotoneCut F)
    (hcorrect : ∀ X, X.card ≤ k + 1 →
      (F X (OrCut a b X) = true ↔ L ⊆ X)) :
    ∀ X, X.card ≤ k → (F X true = true ↔ L ⊆ X) := by
  intro X hX
  constructor
  · intro h
    have hXa : (insert a X).card ≤ k + 1 :=
      (Finset.card_insert_le a X).trans (Nat.add_le_add_right hX 1)
    have hXb : (insert b X).card ≤ k + 1 :=
      (Finset.card_insert_le b X).trans (Nat.add_le_add_right hX 1)
    have ha : F (insert a X) true = true :=
      hmono X (insert a X) true true (Finset.subset_insert a X) (fun _ => rfl) h
    have hb : F (insert b X) true = true :=
      hmono X (insert b X) true true (Finset.subset_insert b X) (fun _ => rfl) h
    have haCut : OrCut a b (insert a X) = true := by simp [OrCut]
    have hbCut : OrCut a b (insert b X) = true := by simp [OrCut]
    have hLa := (hcorrect (insert a X) hXa).mp (haCut ▸ ha)
    have hLb := (hcorrect (insert b X) hXb).mp (hbCut ▸ hb)
    intro p hp
    have hpa := Finset.mem_insert.mp (hLa hp)
    have hpb := Finset.mem_insert.mp (hLb hp)
    rcases hpa with hpa | hpX
    · rcases hpb with hpb | hpX
      · exact False.elim (hab (hpa.symm.trans hpb))
      · exact hpX
    · exact hpX
  · intro hLX
    have h := (hcorrect X (hX.trans (Nat.le_succ k))).mpr hLX
    exact hmono X X (OrCut a b X) true (Finset.Subset.refl X) (fun _ => rfl) h

theorem singleton_cut_leak_omits_endpoints
    (F : Finset α → Bool → Bool) (a b : α) (L X : Finset α) (k : ℕ)
    (hcorrect : ∀ Y, Y.card ≤ k →
      (F Y (OrCut a b Y) = true ↔ L ⊆ Y))
    (hX : X.card ≤ k) (htrue : F X true = true) (hbad : ¬ L ⊆ X) :
    a ∉ X ∧ b ∉ X := by
  have hcut : OrCut a b X ≠ true := by
    intro hc
    exact hbad ((hcorrect X hX).mp (hc ▸ htrue))
  simpa [OrCut, not_or] using hcut

theorem singleton_context_redundant
    (a b : α) (L C : Finset α) (hab : a ≠ b)
    (ha : L ⊆ insert a C) (hb : L ⊆ insert b C) : L ⊆ C := by
  intro p hp
  rcases Finset.mem_insert.mp (ha hp) with hpa | hpC
  · rcases Finset.mem_insert.mp (hb hp) with hpb | hpC
    · exact False.elim (hab (hpa.symm.trans hpb))
    · exact hpC
  · exact hpC

theorem foreign_line_plus_point_misses_target
    (L K : Finset α) (p : α) (hL : 3 ≤ L.card)
    (hLK : (L ∩ K).card ≤ 1) : ¬ L ⊆ insert p K := by
  intro hsub
  have hsmall : L ⊆ insert p (L ∩ K) := by
    intro a ha
    rcases Finset.mem_insert.mp (hsub ha) with hap | haK
    · exact Finset.mem_insert.mpr (Or.inl hap)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_inter.mpr ⟨ha, haK⟩))
  have hc := (Finset.card_le_card hsmall).trans (Finset.card_insert_le p (L ∩ K))
  omega

theorem two_factor_tail_has_no_input
    (F : Finset α → Bool) (p : α) (L K : Finset α)
    (hmono : ∀ X Y, X ⊆ Y → F X = true → F Y = true)
    (hL : L.card = 4) (hK : K.card = 4)
    (hLK : (L ∩ K).card ≤ 1) (hFK : F K = true)
    (hcorrect : ∀ X, X.card ≤ 5 →
      (F X = true ∧ p ∈ X ↔ L ⊆ X)) : False := by
  have hcard : (insert p K).card ≤ 5 := by
    have h := Finset.card_insert_le p K
    omega
  have htrue : F (insert p K) = true :=
    hmono K (insert p K) (Finset.subset_insert p K) hFK
  have hsub := (hcorrect (insert p K) hcard).mp ⟨htrue, by simp⟩
  exact foreign_line_plus_point_misses_target L K p (by omega) hLK hsub

end PEqualNP.Outside.Meta921Strategy
