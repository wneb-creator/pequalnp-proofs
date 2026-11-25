namespace PEqualNP.Outside.L_meta_3451_aux.Small

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma embedding_of_card_two {α : Type} [DecidableEq α] (S : Finset α) (hs : S.card = 2) :
    ∃ e : Fin 2 ↪ α, ∀ x ∈ S, ∃ i : Fin 2, x = e i := by
  classical
  have hc : Fintype.card {x // x ∈ S} = 2 := by simpa using hs
  let e := (Fintype.equivFinOfCardEq hc).symm
  let emb : Fin 2 ↪ α := ⟨fun i => (e i).val, by
    intro i j h
    apply e.injective
    exact Subtype.ext h⟩
  refine ⟨emb, ?_⟩
  intro x hx
  refine ⟨e.symm ⟨x, hx⟩, ?_⟩
  change x = (e (e.symm ⟨x, hx⟩)).val
  rw [e.apply_symm_apply]

lemma normalize_three (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hm : Monotone2 C) (hb : NestedCover.ReadsBack (N + N) C)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (small : C.size ≤ 3) : Star.NormalForm N I C := by
  classical
  let P := Dependency.activePoints N I
  let L := Dependency.activeLines N I
  have point_mem (p l : Fin N) (hi : I p l) : p ∈ P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hi⟩⟩
  have line_mem (p l : Fin N) (hi : I p l) : l ∈ L :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hi⟩⟩
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hm g hg).2
  by_cases hp0 : P = ∅
  · apply no_incidence N I C
    intro p l hi
    have hp := point_mem p l hi
    rw [hp0] at hp
    exact Finset.notMem_empty p hp
  by_cases hl0 : L = ∅
  · apply no_incidence N I C
    intro p l hi
    have hl := line_mem p l hi
    rw [hl0] at hl
    exact Finset.notMem_empty l hl
  by_cases hp1 : P.card = 1
  · obtain ⟨p0, hp⟩ := Finset.card_eq_one.mp hp1
    apply Star.point_star N I C hfan sem p0
    intro p l hi
    have h := point_mem p l hi
    rw [hp] at h
    exact Finset.mem_singleton.mp h
  by_cases hl1 : L.card = 1
  · obtain ⟨l0, hl⟩ := Finset.card_eq_one.mp hl1
    apply Star.line_star N I C hfan sem l0
    intro p l hi
    have h := line_mem p l hi
    rw [hl] at h
    exact Finset.mem_singleton.mp h
  have hp_pos : 0 < P.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hp0)
  have hl_pos : 0 < L.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hl0)
  have total : P.card + L.card ≤ C.size + 1 :=
    Dependency.incidence_active_bound N I C hfan sem
  have hp2 : P.card = 2 := by omega
  have hl2 : L.card = 2 := by omega
  obtain ⟨ep, coverP⟩ := embedding_of_card_two P hp2
  obtain ⟨el, coverL⟩ := embedding_of_card_two L hl2
  apply Support.normalize_supported I ep el ?_ C hm hb sem
  intro p l hi
  obtain ⟨a, ha⟩ := coverP p (point_mem p l hi)
  obtain ⟨b, hb⟩ := coverL l (line_mem p l hi)
  exact ⟨a, b, ha, hb⟩

end PEqualNP.Outside.L_meta_3451_aux.Small
