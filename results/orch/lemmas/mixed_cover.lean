import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2602_aux

open scoped Pointwise

def incidenceNeighborhood (S : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun l => ∃ p ∈ S,
    p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

def incidenceShifts : Finset (Fin 13) := {0, 12, 10, 4}

set_option synthInstance.maxSize 4096 in
lemma incidence_shift_iff : ∀ p l : Fin 13,
    (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ↔
    ∃ t ∈ incidenceShifts, p + t = l := by
  decide

lemma incidenceNeighborhood_eq_add (S : Finset (Fin 13)) :
    incidenceNeighborhood S = S + incidenceShifts := by
  ext l
  simp only [incidenceNeighborhood, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_add, incidence_shift_iff]

lemma incidence_neighborhood_expand : ∀ S : Finset (Fin 13),
    S.Nonempty → incidenceNeighborhood S ≠ Finset.univ →
    S.card + 3 ≤ (incidenceNeighborhood S).card := by
  intro S hs hn
  have ht : incidenceShifts.Nonempty := ⟨0, by simp [incidenceShifts]⟩
  have hfour : incidenceShifts.card = 4 := by decide
  have hcd := ZMod.cauchy_davenport (p := 13)
    (s := show Finset (ZMod 13) from S)
    (t := show Finset (ZMod 13) from incidenceShifts) (by decide) hs ht
  change min 13 (S.card + incidenceShifts.card - 1) ≤ (S + incidenceShifts).card at hcd
  rw [← incidenceNeighborhood_eq_add, hfour] at hcd
  have hlt : (incidenceNeighborhood S).card < 13 := by
    have h := Finset.card_lt_card
      (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hn⟩)
    simpa using h
  simp only [min_le_iff] at hcd
  omega

lemma incidence_mixed_cover_bound (P L : Finset (Fin 13))
    (hP : P ≠ Finset.univ) (hL : L ≠ Finset.univ)
    (cover : ∀ p l : Fin 13,
      (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) → p ∈ P ∨ l ∈ L) :
    16 ≤ P.card + L.card := by
  have hS : (Finset.univ \ P).Nonempty := by
    by_contra h
    apply hP
    apply Finset.eq_univ_of_forall
    intro p
    by_contra hp
    apply h
    exact ⟨p, by simp [hp]⟩
  have hsub : incidenceNeighborhood (Finset.univ \ P) ⊆ L := by
    intro l hl
    obtain ⟨p, hp, hi⟩ := (Finset.mem_filter.mp hl).2
    exact (cover p l hi).resolve_left (Finset.mem_sdiff.mp hp).2
  have hnot : incidenceNeighborhood (Finset.univ \ P) ≠ Finset.univ := by
    intro he
    apply hL
    apply Finset.eq_univ_of_forall
    intro l
    apply hsub
    rw [he]
    exact Finset.mem_univ l
  have hbound := incidence_neighborhood_expand (Finset.univ \ P) hS hnot
  have hcard := Finset.card_le_card hsub
  have hsum := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  have hu : (Finset.univ : Finset (Fin 13)).card = 13 := by decide
  omega

end PEqualNP.Outside.L_meta_2602_aux
