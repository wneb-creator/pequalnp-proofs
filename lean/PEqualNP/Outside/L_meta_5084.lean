import Mathlib
import PEqualNP.Defs

-- Every pairwise union u ∪ v has an element with P exactly when every u has one
-- or every v has one.
namespace PEqualNP.Outside.L_meta_5084

theorem product_main (d : ℕ) (U V : Finset (Finset (Fin d))) (P : Fin d → Prop) :
    (∀ t ∈ U.biUnion (fun u => V.image (u ∪ ·)), ∃ i ∈ t, P i) ↔
      (∀ t ∈ U, ∃ i ∈ t, P i) ∨ (∀ t ∈ V, ∃ i ∈ t, P i) := by
  constructor
  · intro h
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hU, hV⟩ := hcon
    apply hU
    intro u hu
    by_contra hnu
    apply hV
    intro v hv
    have hmem : u ∪ v ∈ U.biUnion (fun u => V.image (u ∪ ·)) := by
      rw [Finset.mem_biUnion]
      exact ⟨u, hu, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩
    obtain ⟨i, hi, hPi⟩ := h (u ∪ v) hmem
    rcases Finset.mem_union.mp hi with hiu | hiv
    · exact absurd ⟨i, hiu, hPi⟩ hnu
    · exact ⟨i, hiv, hPi⟩
  · intro h t ht
    rw [Finset.mem_biUnion] at ht
    obtain ⟨u, hu, htu⟩ := ht
    rw [Finset.mem_image] at htu
    obtain ⟨v, hv, hvt⟩ := htu
    rw [← hvt]
    rcases h with h | h
    · obtain ⟨i, hi, hPi⟩ := h u hu
      exact ⟨i, Finset.mem_union_left _ hi, hPi⟩
    · obtain ⟨i, hi, hPi⟩ := h v hv
      exact ⟨i, Finset.mem_union_right _ hi, hPi⟩

end PEqualNP.Outside.L_meta_5084

theorem PEqualNP.Outside.L_meta_5084 : ∀ (x1 : ℕ) (x2 x3 : Finset (Finset (Fin x1))) (x4 : Fin x1 → Prop), (∀ x5 ∈ x2.biUnion fun (x6 : Finset (Fin x1)) => Finset.image (fun (x7 : Finset (Fin x1)) => x6 ∪ x7) x3, ∃ x7 ∈ x5, x4 x7) ↔ (∀ x5 ∈ x2, ∃ x7 ∈ x5, x4 x7) ∨ ∀ x5 ∈ x3, ∃ x7 ∈ x5, x4 x7 := by
  intro d U V P
  exact PEqualNP.Outside.L_meta_5084.product_main d U V P
