import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.NoC4

lemma common_lines_card (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p p' : Fin N) (hne : p ≠ p') :
    (Finset.univ.filter (fun l => I p l ∧ I p' l)).card = 1 := by
  obtain ⟨l, hl, hu⟩ := hpair p p' hne
  apply Finset.card_eq_one.mpr
  refine ⟨l, ?_⟩
  ext l'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact ⟨fun h => hu l' h, fun h => h ▸ hl⟩

lemma common_points_card_le_one (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hpair : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (l l' : Fin N) (hne : l ≠ l') :
    (Finset.univ.filter (fun p => I p l ∧ I p l')).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  by_contra hpp'
  have hpI : I p l ∧ I p l' := by simpa using hp
  have hpI' : I p' l ∧ I p' l' := by simpa using hp'
  obtain ⟨a, ha, hu⟩ := hpair p p' hpp'
  exact hne ((hu l ⟨hpI.1, hpI'.1⟩).trans (hu l' ⟨hpI.2, hpI'.2⟩).symm)

end PEqualNP.Outside.L_meta_2583_aux.NoC4
