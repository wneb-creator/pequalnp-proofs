import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerRectangles

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def edgePairs : Finset (Fin 16 × Fin 16) := {(0, 5), (0, 6), (0, 8), (0, 13), (1, 5), (1, 7), (1, 12), (1, 15), (2, 6), (2, 11), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (3, 14), (4, 7), (4, 10), (4, 11), (4, 13)}

def dirtyPairs : Finset (Fin 16 × Fin 16) := {(1, 13), (2, 13), (5, 11), (5, 13), (5, 14), (6, 7), (6, 12), (6, 13), (7, 13), (7, 14), (11, 12), (11, 13), (12, 13), (13, 14), (13, 15)}

def allowed (u v : Fin 16) : Prop :=
  (u, v) ∈ edgePairs ∨ (v, u) ∈ edgePairs ∨
  (u, v) ∈ dirtyPairs ∨ (v, u) ∈ dirtyPairs

instance (u v : Fin 16) : Decidable (allowed u v) := inferInstanceAs
  (Decidable ((u, v) ∈ edgePairs ∨ (v, u) ∈ edgePairs ∨
    (u, v) ∈ dirtyPairs ∨ (v, u) ∈ dirtyPairs))

def points : Finset (Fin 16) := {0, 1, 2, 3, 4}

def neighbors (p : Fin 16) : Finset (Fin 16) :=
  Finset.univ.filter fun l => (p, l) ∈ edgePairs

def owned (P : Finset (Fin 16)) : Finset (Fin 16 × Fin 16) :=
  edgePairs.filter fun e => e.1 ∈ P ∧ ∀ p ∈ P, allowed p e.2

def covered (L R : Finset (Fin 16)) : Finset (Fin 16 × Fin 16) :=
  edgePairs.filter fun e => (e.1 ∈ L ∧ e.2 ∈ R) ∨ (e.1 ∈ R ∧ e.2 ∈ L)

def AllAllowed (L R : Finset (Fin 16)) : Prop :=
  ∀ u ∈ L, ∀ v ∈ R, allowed u v

instance (L R : Finset (Fin 16)) : Decidable (AllAllowed L R) :=
  inferInstanceAs (Decidable (∀ u ∈ L, ∀ v ∈ R, allowed u v))

theorem allowed_symm (u v : Fin 16) (h : allowed u v) : allowed v u := by
  rcases h with h | h | h | h <;> simp only [allowed] <;> tauto

theorem edge_sides : ∀ e ∈ edgePairs, e.1 ∈ points ∧ e.2 ∉ points := by
  decide +kernel

theorem no_point_pair : ∀ u ∈ points, ∀ v ∈ points, ¬ allowed u v := by
  decide +kernel

theorem no_self : ∀ u : Fin 16, ¬ allowed u u := by
  decide +kernel

theorem owned_small_table : ∀ P ∈ points.powerset,
    (owned P).card ≤ 4 ∧
    (4 ≤ (owned P).card → ∃ p ∈ points, P = {p}) := by
  have checked : (points.powerset.toList.all fun P => decide
      ((owned P).card ≤ 4 ∧
        (4 ≤ (owned P).card → ∃ p ∈ points, P = {p}))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, Finset.mem_toList, decide_eq_true_eq] using checked

def rightAllowed (p : Fin 16) : Finset (Fin 16) :=
  Finset.univ.filter fun l => allowed p l

def leftCommon (p : Fin 16) : Finset (Fin 16) :=
  Finset.univ.filter fun u => ∀ l ∈ neighbors p, allowed u l

def shapes : Finset (Finset (Fin 16) × Finset (Fin 16)) := {({0}, {5, 6, 8, 13}),
  ({1}, {5, 7, 12, 13, 15}),
  ({1}, {5, 7, 12, 15}),
  ({2}, {6, 11, 13, 14, 15}),
  ({2}, {6, 11, 14, 15}),
  ({3}, {9, 12, 13, 14}),
  ({4}, {7, 10, 11, 13}),
  ({1, 13}, {5, 7, 12, 15}),
  ({2, 13}, {6, 11, 14, 15})}

theorem owner_shapes_table : ∀ p ∈ points,
    ∀ L ∈ (leftCommon p).powerset, ∀ R ∈ (rightAllowed p).powerset,
    p ∈ L → neighbors p ⊆ R → AllAllowed L R → (L, R) ∈ shapes := by
  have checked : (points.toList.all fun p =>
      (leftCommon p).powerset.toList.all fun L =>
        (rightAllowed p).powerset.toList.all fun R =>
          decide (p ∈ L → neighbors p ⊆ R → AllAllowed L R → (L, R) ∈ shapes)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, Finset.mem_toList, decide_eq_true_eq] using checked

theorem shapes_have_four : ∀ S ∈ shapes, (covered S.1 S.2).card = 4 := by
  have checked : (shapes.toList.all fun S => decide ((covered S.1 S.2).card = 4)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, Finset.mem_toList, decide_eq_true_eq] using checked

theorem covered_swap (L R : Finset (Fin 16)) : covered L R = covered R L := by
  ext e
  simp only [covered, Finset.mem_filter]
  tauto

theorem allAllowed_swap {L R : Finset (Fin 16)} (h : AllAllowed L R) : AllAllowed R L := by
  intro u hu v hv
  exact allowed_symm _ _ (h v hv u hu)

theorem no_right_point {L R : Finset (Fin 16)} (h : AllAllowed L R)
    (hL : (L ∩ points).Nonempty) : ∀ p ∈ points, p ∉ R := by
  obtain ⟨q, hq⟩ := hL
  obtain ⟨hqL, hqp⟩ := Finset.mem_inter.mp hq
  intro p hp hpR
  exact no_point_pair q hqp p hp (h q hqL p hpR)

theorem covered_subset_owned {L R : Finset (Fin 16)} (h : AllAllowed L R)
    (hL : (L ∩ points).Nonempty) : covered L R ⊆ owned (L ∩ points) := by
  intro e he
  obtain ⟨hedge, hcross⟩ := Finset.mem_filter.mp he
  have hs := edge_sides e hedge
  have hn := no_right_point h hL e.1 hs.1
  have hc : e.1 ∈ L ∧ e.2 ∈ R := by tauto
  apply Finset.mem_filter.mpr
  refine ⟨hedge, Finset.mem_inter.mpr ⟨hc.1, hs.1⟩, ?_⟩
  intro p hp
  exact h p (Finset.mem_inter.mp hp).1 e.2 hc.2

theorem max_four (L R : Finset (Fin 16)) (h : AllAllowed L R) :
    (covered L R).card ≤ 4 := by
  by_cases hL : (L ∩ points).Nonempty
  · have ht := owned_small_table (L ∩ points)
      (Finset.mem_powerset.mpr Finset.inter_subset_right)
    exact (Finset.card_le_card (covered_subset_owned h hL)).trans ht.1
  by_cases hR : (R ∩ points).Nonempty
  · rw [covered_swap]
    have ht := owned_small_table (R ∩ points)
      (Finset.mem_powerset.mpr Finset.inter_subset_right)
    exact (Finset.card_le_card (covered_subset_owned (allAllowed_swap h) hR)).trans ht.1
  have hempty : covered L R = ∅ := by
    apply Finset.eq_empty_iff_forall_not_mem.mpr
    intro e he
    obtain ⟨hedge, hc⟩ := Finset.mem_filter.mp he
    have hp := (edge_sides e hedge).1
    rcases hc with hc | hc
    · exact hL ⟨e.1, Finset.mem_inter.mpr ⟨hc.1, hp⟩⟩
    · exact hR ⟨e.1, Finset.mem_inter.mpr ⟨hc.1, hp⟩⟩
  simp [hempty]

theorem oriented_classification (L R : Finset (Fin 16)) (h : AllAllowed L R)
    (hL : (L ∩ points).Nonempty) (hfour : 4 ≤ (covered L R).card) :
    (L, R) ∈ shapes := by
  have ht := owned_small_table (L ∩ points)
    (Finset.mem_powerset.mpr Finset.inter_subset_right)
  have hsub := covered_subset_owned h hL
  have hcard := Finset.card_le_card hsub
  obtain ⟨p, hp, hLP⟩ := ht.2 (hfour.trans hcard)
  have hpL : p ∈ L := by
    have hm : p ∈ L ∩ points := by rw [hLP]; simp
    exact (Finset.mem_inter.mp hm).1
  have heq : covered L R = owned (L ∩ points) :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hn : neighbors p ⊆ R := by
    intro l hl
    have he : (p, l) ∈ edgePairs := (Finset.mem_filter.mp hl).2
    have howned : (p, l) ∈ owned (L ∩ points) := by
      apply Finset.mem_filter.mpr
      refine ⟨he, ?_, ?_⟩
      · rw [hLP]; simp
      · intro q hq
        have hqp : q = p := by simpa [hLP] using hq
        subst q
        exact Or.inl he
    rw [← heq] at howned
    have hc := (Finset.mem_filter.mp howned).2
    have hnr := no_right_point h hL p hp
    tauto
  apply owner_shapes_table p hp L _ R _ hpL hn h
  · apply Finset.mem_powerset.mpr
    intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro l hl
    exact h u hu l (hn hl)
  · apply Finset.mem_powerset.mpr
    intro l hl
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h p hpL l hl⟩

theorem classify_four (L R : Finset (Fin 16)) (h : AllAllowed L R)
    (hfour : 4 ≤ (covered L R).card) :
    (L, R) ∈ shapes ∨ (R, L) ∈ shapes := by
  by_cases hL : (L ∩ points).Nonempty
  · exact Or.inl (oriented_classification L R h hL hfour)
  have hR : (R ∩ points).Nonempty := by
    have hn : (covered L R).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨e, he⟩ := hn
    obtain ⟨hedge, hc⟩ := Finset.mem_filter.mp he
    have hp := (edge_sides e hedge).1
    rcases hc with hc | hc
    · exact False.elim (hL ⟨e.1, Finset.mem_inter.mpr ⟨hc.1, hp⟩⟩)
    · exact ⟨e.1, Finset.mem_inter.mpr ⟨hc.1, hp⟩⟩
  apply Or.inr
  apply oriented_classification R L (allAllowed_swap h) hR
  simpa only [covered_swap R L] using hfour

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerRectangles
