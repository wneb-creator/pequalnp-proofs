import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.JointLambdaGeometry

open PEqualNP.TopForm

noncomputable def unownedAcross {n : ℕ} (S X Y : Finset (Fin n))
    (owned : Finset (Sym2 (Fin n))) : Finset (Fin n) := by
  classical
  exact (S ∩ X).filter (fun x => ∃ y ∈ Y, s(x, y) ∉ owned)

lemma unowned_across_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (S X Y : Finset (Fin n)) (owned : Finset (Sym2 (Fin n)))
    (c : Fin n) (hstar : ∀ v ∈ S, G.Adj c v) (howned : ∀ v ∈ S, s(c, v) ∈ owned)
    (hcross : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) :
    (unownedAcross S X Y owned).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro x hx z hz
  obtain ⟨hxSX, y, hyY, hxy⟩ := Finset.mem_filter.mp hx
  have hzSX := (Finset.mem_filter.mp hz).1
  have hxS := (Finset.mem_inter.mp hxSX).1
  have hxX := (Finset.mem_inter.mp hxSX).2
  have hzS := (Finset.mem_inter.mp hzSX).1
  have hzX := (Finset.mem_inter.mp hzSX).2
  have hcy : c ≠ y := by
    intro he
    apply hxy
    rw [← he]
    simpa only [Sym2.eq_swap] using howned x hxS
  exact Finset.card_le_one.mp (hG c y hcy) x
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar x hxS, (hcross x hxX y hyY).symm⟩)
    z
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar z hzS, (hcross z hzX y hyY).symm⟩)

lemma shared_support_owned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (S X Y : Finset (Fin n)) (owned : Finset (Sym2 (Fin n)))
    (c : Fin n) (hstar : ∀ v ∈ S, G.Adj c v) (howned : ∀ v ∈ S, s(c, v) ∈ owned)
    (hcross : ∀ x ∈ X, ∀ y ∈ Y, G.Adj x y) (hSX : S ⊆ X) (hS : 2 ≤ S.card) :
    ∀ x ∈ S, ∀ y ∈ Y, s(x, y) ∈ owned := by
  intro x hx y hy
  by_contra hxy
  have hcy : c ≠ y := by
    intro he
    apply hxy
    rw [← he]
    simpa only [Sym2.eq_swap] using howned x hx
  have hs : S ⊆ Finset.univ.filter (fun v => G.Adj c v ∧ G.Adj y v) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hstar v hv, (hcross v (hSX hv) y hy).symm⟩
  have hc := (Finset.card_le_card hs).trans (hG c y hcy)
  omega

noncomputable def unownedJointInputs {n : ℕ} (S B C D : Finset (Fin n))
    (owned : Finset (Sym2 (Fin n))) : Finset (Fin n) := by
  classical
  exact S.filter (fun v => ∃ w ∈ B,
    ((v ∈ C ∨ w ∈ C) ∧ (v ∈ D ∨ w ∈ D)) ∧ s(v, w) ∉ owned)

lemma unowned_joint_inputs_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (S A B C D : Finset (Fin n))
    (owned : Finset (Sym2 (Fin n))) (c : Fin n) (hSA : S ⊆ A) (hCD : Disjoint C D)
    (hstar : ∀ v ∈ S, G.Adj c v) (howned : ∀ v ∈ S, s(c, v) ∈ owned)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b) :
    (unownedJointInputs S B C D owned).card ≤ 2 := by
  classical
  have hsub : unownedJointInputs S B C D owned ⊆
      unownedAcross S (A ∩ C) (B ∩ D) owned ∪ unownedAcross S (A ∩ D) (B ∩ C) owned := by
    intro v hv
    obtain ⟨hvS, w, hwB, ⟨hvC | hwC, hvD | hwD⟩, hvw⟩ := Finset.mem_filter.mp hv
    · exact (Finset.disjoint_left.mp hCD hvC hvD).elim
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hvS, Finset.mem_inter.mpr ⟨hSA hvS, hvC⟩⟩,
          w, Finset.mem_inter.mpr ⟨hwB, hwD⟩, hvw⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_inter.mpr ⟨hvS, Finset.mem_inter.mpr ⟨hSA hvS, hvD⟩⟩,
          w, Finset.mem_inter.mpr ⟨hwB, hwC⟩, hvw⟩)
    · exact (Finset.disjoint_left.mp hCD hwC hwD).elim
  have h₁ := unowned_across_small G hG S (A ∩ C) (B ∩ D) owned c hstar howned (by
    intro x hx y hy
    exact hjoint x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
      (Or.inl (Finset.mem_inter.mp hx).2) (Or.inr (Finset.mem_inter.mp hy).2))
  have h₂ := unowned_across_small G hG S (A ∩ D) (B ∩ C) owned c hstar howned (by
    intro x hx y hy
    exact hjoint x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
      (Or.inr (Finset.mem_inter.mp hy).2) (Or.inl (Finset.mem_inter.mp hx).2))
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le (unownedAcross S (A ∩ C) (B ∩ D) owned)
    (unownedAcross S (A ∩ D) (B ∩ C) owned)
  omega

lemma shared_joint_inputs_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (S A B C D : Finset (Fin n))
    (owned : Finset (Sym2 (Fin n))) (c : Fin n) (hSA : S ⊆ A) (hSC : S ⊆ C)
    (hCD : Disjoint C D) (hS : 2 ≤ S.card)
    (hstar : ∀ v ∈ S, G.Adj c v) (howned : ∀ v ∈ S, s(c, v) ∈ owned)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b) :
    unownedJointInputs S B C D owned = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvS, w, hwB, ⟨hvC, hvD | hwD⟩, hvw⟩ := Finset.mem_filter.mp hv
  · exact Finset.disjoint_left.mp hCD (hSC hvS) hvD
  · apply hvw
    exact shared_support_owned G hG S (A ∩ C) (B ∩ D) owned c hstar howned (by
      intro x hx y hy
      exact hjoint x (Finset.mem_inter.mp hx).1 y (Finset.mem_inter.mp hy).1
        (Or.inl (Finset.mem_inter.mp hx).2) (Or.inr (Finset.mem_inter.mp hy).2))
      (fun x hx => Finset.mem_inter.mpr ⟨hSA hx, hSC hx⟩) hS v hvS w (Finset.mem_inter.mpr ⟨hwB, hwD⟩)

end PEqualNP.Outside.L_meta_1477.JointLambdaGeometry
