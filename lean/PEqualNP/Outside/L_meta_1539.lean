import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_1539 : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (P : Finset (K × K)) (a m : K) (T : Finset K), 2 * P.card < Fintype.card K → 2 * T.card ≤ Fintype.card K → ∃ b : K, (∀ pt ∈ P, pt.2 ≠ m * pt.1 + b) ∧ m * a + b ∉ T := by
  intro K _ _ _ P a m T hP hT
  let Bad : Finset K := P.image (fun pt => pt.2 - m * pt.1) ∪ T.image (fun t => t - m * a)
  have hcard : Bad.card < (Finset.univ : Finset K).card := by
    have h1 : Bad.card ≤ P.card + T.card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)
    rw [Finset.card_univ]
    omega
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨b, ?_, ?_⟩
  · intro pt hpt heq
    apply hb
    apply Finset.mem_union_left
    exact Finset.mem_image.2 ⟨pt, hpt, by rw [heq]; ring⟩
  · intro hin
    apply hb
    apply Finset.mem_union_right
    exact Finset.mem_image.2 ⟨m * a + b, hin, by ring⟩
