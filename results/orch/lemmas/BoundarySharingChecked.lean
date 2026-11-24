import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.BoundarySharing

open PEqualNP.TopForm

lemma boundary_common_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (B Q : Finset (Fin n)) (q r a b : Fin n)
    (hboundary : ∀ v ∈ B, G.Adj q v) (hq : q ∉ Q) (hr : r ∈ Q)
    (ha : a ∈ B) (hb : b ∈ B) (har : G.Adj a r) (hbr : G.Adj b r) : a = b := by
  have hqr : q ≠ r := by
    rintro rfl
    exact hq hr
  apply Finset.card_le_one.mp (hG q r hqr)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hboundary a ha, har.symm⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hboundary b hb, hbr.symm⟩

lemma boundary_activity_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (R : Fin n → Fin n → Prop) [DecidableRel R]
    (B Q T : Finset (Fin n)) (q : Fin n)
    (hboundary : ∀ b ∈ B, G.Adj q b) (hq : q ∉ Q) (hdis : Disjoint B Q)
    (hcross : ∀ b ∈ B, ∀ r ∈ Q, R b r → G.Adj b r)
    (hcover : ∀ b ∈ B, ∀ r ∈ Q, R b r → b ∈ T ∨ r ∈ T) :
    (B.filter (fun b => ∃ r ∈ Q, R b r)).card ≤ T.card := by
  classical
  let A := B.filter (fun b => ∃ r ∈ Q, R b r)
  change A.card ≤ T.card
  have neighbor (b : A) (hb : b.val ∉ T) :
      ∃ r : Fin n, r ∈ Q ∧ R b.val r ∧ r ∈ T := by
    obtain ⟨hbB, r, hrQ, hbr⟩ := Finset.mem_filter.mp b.property
    exact ⟨r, hrQ, hbr, (hcover b.val hbB r hrQ hbr).resolve_left hb⟩
  let f : A → T := fun b =>
    if hb : b.val ∈ T then ⟨b.val, hb⟩
    else ⟨Classical.choose (neighbor b hb), (Classical.choose_spec (neighbor b hb)).2.2⟩
  have hinj : Function.Injective f := by
    intro b c he
    apply Subtype.ext
    have heval : (f b).val = (f c).val := congrArg Subtype.val he
    have hbB : b.val ∈ B := (Finset.mem_filter.mp b.property).1
    have hcB : c.val ∈ B := (Finset.mem_filter.mp c.property).1
    by_cases hb : b.val ∈ T
    · by_cases hc : c.val ∈ T
      · simpa only [f, dif_pos hb, dif_pos hc] using heval
      · simp only [f, dif_pos hb, dif_neg hc] at heval
        have hbQ : b.val ∈ Q := by
          rw [heval]
          exact (Classical.choose_spec (neighbor c hc)).1
        exact (Finset.disjoint_left.mp hdis hbB hbQ).elim
    · by_cases hc : c.val ∈ T
      · simp only [f, dif_neg hb, dif_pos hc] at heval
        have hcQ : c.val ∈ Q := by
          rw [← heval]
          exact (Classical.choose_spec (neighbor b hb)).1
        exact (Finset.disjoint_left.mp hdis hcB hcQ).elim
      · simp only [f, dif_neg hb, dif_neg hc] at heval
        have hbN := Classical.choose_spec (neighbor b hb)
        have hcN := Classical.choose_spec (neighbor c hc)
        have hcR : R c.val (Classical.choose (neighbor b hb)) := by
          rw [heval]
          exact hcN.2.1
        exact boundary_common_unique G hG B Q q _ b.val c.val hboundary hq hbN.1
          hbB hcB (hcross b.val hbB _ hbN.1 hbN.2.1)
          (hcross c.val hcB _ hbN.1 hcR)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

lemma boundary_activity_two {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (R : Fin n → Fin n → Prop) [DecidableRel R]
    (B Q T : Finset (Fin n)) (q : Fin n)
    (hboundary : ∀ b ∈ B, G.Adj q b) (hq : q ∉ Q) (hdis : Disjoint B Q)
    (hcross : ∀ b ∈ B, ∀ r ∈ Q, R b r → G.Adj b r)
    (hcover : ∀ b ∈ B, ∀ r ∈ Q, R b r → b ∈ T ∨ r ∈ T)
    (hT : T.card ≤ 2) :
    (B.filter (fun b => ∃ r ∈ Q, R b r)).card ≤ 2 :=
  (boundary_activity_card G hG R B Q T q hboundary hq hdis hcross hcover).trans hT

end PEqualNP.Outside.L_meta_1477.BoundarySharing
