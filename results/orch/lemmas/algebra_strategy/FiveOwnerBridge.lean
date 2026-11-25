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

def pointSubsets : List (Finset (Fin 16)) :=
  [{}, {0}, {1}, {2}, {3}, {4}, {0, 1}, {0, 2}, {0, 3}, {0, 4}, {1, 2}, {1, 3}, {1, 4}, {2, 3}, {2, 4}, {3, 4}, {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 2, 3}, {0, 2, 4}, {0, 3, 4}, {1, 2, 3}, {1, 2, 4}, {1, 3, 4}, {2, 3, 4}, {0, 1, 2, 3}, {0, 1, 2, 4}, {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 4}]

theorem owned_small_table : ∀ P ∈ points.powerset,
    (owned P).card ≤ 4 ∧
    (4 ≤ (owned P).card → ∃ p ∈ points, P = {p}) := by
  have hsets : pointSubsets.toFinset = points.powerset := by decide +kernel
  have checked : (pointSubsets.all fun P => decide
      ((owned P).card ≤ 4 ∧
        (4 ≤ (owned P).card → ∃ p ∈ points, P = {p}))) = true := by
    decide +kernel
  intro P hP
  have hm : P ∈ pointSubsets := by
    rw [← List.mem_toFinset, hsets]
    exact hP
  exact of_decide_eq_true ((List.all_eq_true.mp checked) P hm)

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

theorem owner_bounds_table : ∀ p ∈ points,
    leftCommon p ⊆ {p, 13} ∧ rightAllowed p ⊆ insert 13 (neighbors p) := by
  decide +kernel

theorem between_pair (L : Finset (Fin 16)) (p q : Fin 16)
    (hp : p ∈ L) (hupper : L ⊆ {p, q}) : L = {p} ∨ L = {p, q} := by
  by_cases hq : q ∈ L
  · exact Or.inr (Finset.Subset.antisymm hupper
      (Finset.insert_subset_iff.mpr ⟨hp, Finset.singleton_subset_iff.mpr hq⟩))
  · apply Or.inl
    apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hp)
    intro x hx
    have hh := hupper hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    rcases hh with hh | hh
    · exact hh
    · subst x
      exact False.elim (hq hx)

theorem between_insert (R S : Finset (Fin 16)) (q : Fin 16)
    (hlower : S ⊆ R) (hupper : R ⊆ insert q S) : R = S ∨ R = insert q S := by
  by_cases hq : q ∈ R
  · exact Or.inr (Finset.Subset.antisymm hupper
      (Finset.insert_subset_iff.mpr ⟨hq, hlower⟩))
  · apply Or.inl
    apply Finset.Subset.antisymm _ hlower
    intro x hx
    have hh := Finset.mem_insert.mp (hupper hx)
    rcases hh with hh | hh
    · subst x
      exact False.elim (hq hx)
    · exact hh

theorem owner_shapes_table : ∀ p ∈ points,
    ∀ L ∈ (leftCommon p).powerset, ∀ R ∈ (rightAllowed p).powerset,
    p ∈ L → neighbors p ⊆ R → AllAllowed L R → (L, R) ∈ shapes := by
  have small : ∀ p ∈ points, ∀ b c : Bool,
      AllAllowed (if b then {p, 13} else {p})
        (if c then insert 13 (neighbors p) else neighbors p) →
      ((if b then {p, 13} else {p}),
        (if c then insert 13 (neighbors p) else neighbors p)) ∈ shapes := by
    decide +kernel
  intro p hp L hL R hR hpL hn hallowed
  have hb := owner_bounds_table p hp
  have hl := between_pair L p 13 hpL ((Finset.mem_powerset.mp hL).trans hb.1)
  have hr := between_insert R (neighbors p) 13 hn ((Finset.mem_powerset.mp hR).trans hb.2)
  rcases hl with hl | hl
  · rcases hr with hr | hr
    · subst L; subst R
      exact small p hp false false hallowed
    · subst L; subst R
      exact small p hp false true hallowed
  · rcases hr with hr | hr
    · subst L; subst R
      exact small p hp true false hallowed
    · subst L; subst R
      exact small p hp true true hallowed

def shapeList : List (Finset (Fin 16) × Finset (Fin 16)) := [({0}, {5, 6, 8, 13}), ({1}, {5, 7, 12, 13, 15}), ({1}, {5, 7, 12, 15}), ({2}, {6, 11, 13, 14, 15}), ({2}, {6, 11, 14, 15}), ({3}, {9, 12, 13, 14}), ({4}, {7, 10, 11, 13}), ({1, 13}, {5, 7, 12, 15}), ({2, 13}, {6, 11, 14, 15})]

theorem shapes_have_four : ∀ S ∈ shapes, (covered S.1 S.2).card = 4 := by
  have hsets : shapeList.toFinset = shapes := by decide +kernel
  have checked : (shapeList.all fun S => decide ((covered S.1 S.2).card = 4)) = true := by
    decide +kernel
  intro S hS
  have hm : S ∈ shapeList := by rw [← List.mem_toFinset, hsets]; exact hS
  exact of_decide_eq_true ((List.all_eq_true.mp checked) S hm)

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
    apply Finset.Subset.antisymm _ (Finset.empty_subset _)
    intro e he
    exfalso
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

def ownerEdges (p : Fin 16) : Finset (Fin 16 × Fin 16) :=
  edgePairs.filter fun e => e.1 = p

def Ordinary (L R : Finset (Fin 16)) : Prop :=
  ∃ p ∈ points, L = {p} ∧ R = neighbors p

instance (L R : Finset (Fin 16)) : Decidable (Ordinary L R) :=
  inferInstanceAs (Decidable (∃ p ∈ points, L = {p} ∧ R = neighbors p))

def dirtyShapes : Finset (Finset (Fin 16) × Finset (Fin 16)) :=
  {({1}, {5, 7, 12, 13, 15}), ({2}, {6, 11, 13, 14, 15}),
   ({1, 13}, {5, 7, 12, 15}), ({2, 13}, {6, 11, 14, 15})}

theorem shape_structure_table : ∀ S ∈ shapes,
    (∃ p ∈ points, covered S.1 S.2 = ownerEdges p) ∧
    (Ordinary S.1 S.2 ∨ S ∈ dirtyShapes) := by
  have hsets : shapeList.toFinset = shapes := by decide +kernel
  have checked : (shapeList.all fun S => decide
      ((∃ p ∈ points, covered S.1 S.2 = ownerEdges p) ∧
        (Ordinary S.1 S.2 ∨ S ∈ dirtyShapes))) = true := by
    decide +kernel
  intro S hS
  have hm : S ∈ shapeList := by rw [← List.mem_toFinset, hsets]; exact hS
  exact of_decide_eq_true ((List.all_eq_true.mp checked) S hm)

theorem owner_witness (L R : Finset (Fin 16)) (h : AllAllowed L R)
    (hfour : 4 ≤ (covered L R).card) :
    ∃ p ∈ points, covered L R = ownerEdges p := by
  rcases classify_four L R h hfour with hshape | hshape
  · exact (shape_structure_table (L, R) hshape).1
  · simpa only [covered_swap R L] using (shape_structure_table (R, L) hshape).1

theorem point_side (L R : Finset (Fin 16)) (h : AllAllowed L R)
    (hfour : 4 ≤ (covered L R).card) :
    Ordinary L R ∨ Ordinary R L ∨ (L, R) ∈ dirtyShapes ∨ (R, L) ∈ dirtyShapes := by
  rcases classify_four L R h hfour with hshape | hshape
  · have ht := (shape_structure_table (L, R) hshape).2
    tauto
  · have ht := (shape_structure_table (R, L) hshape).2
    tauto

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerRectangles


namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerNegatives

def edgePairs : Finset (Fin 16 × Fin 16) := {(0, 5), (0, 6), (0, 8), (0, 13), (1, 5), (1, 7), (1, 12), (1, 15), (2, 6), (2, 11), (2, 14), (2, 15), (3, 9), (3, 12), (3, 13), (3, 14), (4, 7), (4, 10), (4, 11), (4, 13)}

def dirtyPairs : Finset (Fin 16 × Fin 16) := {(1, 13), (2, 13), (5, 11), (5, 13), (5, 14), (6, 7), (6, 12), (6, 13), (7, 13), (7, 14), (11, 12), (11, 13), (12, 13), (13, 14), (13, 15)}

abbrev allowed (u v : Fin 16) : Prop :=
  (u,v) ∈ edgePairs ∨ (v,u) ∈ edgePairs ∨ (u,v) ∈ dirtyPairs ∨ (v,u) ∈ dirtyPairs

abbrev hasEdge (U : Finset (Fin 16)) : Prop := ∃ e ∈ edgePairs, e.1 ∈ U ∧ e.2 ∈ U

def negativeList : List (Finset (Fin 16)) :=
  [{0, 1, 2, 3, 4}, {1, 2, 3, 4, 8}, {2, 3, 4, 5, 8}, {1, 3, 4, 6, 8}, {0, 1, 2, 4, 9}, {1, 2, 4, 8, 9}, {0, 1, 2, 3, 10}, {0, 2, 3, 7, 10}, {1, 2, 3, 8, 10}, {2, 3, 5, 7, 8, 10}, {0, 1, 2, 9, 10}, {0, 1, 3, 10, 11}, {1, 3, 6, 8, 10, 11}, {0, 2, 4, 9, 12}, {2, 4, 5, 8, 9, 12}, {0, 2, 7, 9, 10, 12}, {1, 2, 8, 9, 10, 13}, {2, 5, 7, 8, 9, 10, 12, 13}, {0, 1, 4, 9, 14}, {1, 4, 6, 8, 9, 14}, {0, 1, 9, 10, 11, 14}, {1, 6, 8, 9, 10, 11, 13, 14}, {0, 3, 4, 15}, {3, 4, 5, 6, 8, 15}, {0, 3, 7, 10, 11, 15}, {3, 5, 6, 7, 8, 10, 11, 15}, {0, 4, 9, 12, 14, 15}, {4, 5, 6, 8, 9, 12, 14, 15}, {0, 7, 9, 10, 11, 12, 14, 15}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}]

def family : Finset (Finset (Fin 16)) := negativeList.toFinset

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem family_card : family.card = 30 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem negative_check : negativeList.all (fun U => decide (¬hasEdge U)) = true := by decide +kernel

theorem family_negative (U : Finset (Fin 16)) (hU : U ∈ family) : ¬hasEdge U := by
  have hu : U ∈ negativeList := by simpa [family] using hU
  exact decide_eq_true_eq.mp (List.all_eq_true.mp negative_check U hu)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem pair_check : negativeList.all (fun U => negativeList.all
    (fun V => decide (U = V ∨ hasEdge (U ∪ V)))) = true := by decide +kernel

theorem pair_positive (U V : Finset (Fin 16)) (hU : U ∈ family) (hV : V ∈ family)
    (hne : U ≠ V) : hasEdge (U ∪ V) := by
  have hu : U ∈ negativeList := by simpa [family] using hU
  have hv : V ∈ negativeList := by simpa [family] using hV
  have h := List.all_eq_true.mp (List.all_eq_true.mp pair_check U hu) V hv
  exact (decide_eq_true_eq.mp h).resolve_left hne

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem singleton_count : ∀ v : Fin 16, 4 ≤ (family.filter fun U => v ∈ U).card := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem forbidden_pair_count : ∀ u v : Fin 16, ¬allowed u v →
    3 ≤ (family.filter fun U => u ∈ U ∧ v ∈ U).card := by decide +kernel

def dirtyTemplates : List (Fin 16 × Finset (Fin 16) × Finset (Fin 16)) :=
  [(1, {1}, {5, 7, 12, 13, 15}), (2, {2}, {6, 11, 13, 14, 15}), (1, {1, 13}, {5, 7, 12, 15}), (2, {2, 13}, {6, 11, 14, 15})]

def badOwner (k : Fin 4) : Fin 16 := (dirtyTemplates[k.val]?.getD (0,∅,∅)).1

def badLeft (k : Fin 4) : Finset (Fin 16) := (dirtyTemplates[k.val]?.getD (0,∅,∅)).2.1

def badRight (k : Fin 4) : Finset (Fin 16) := (dirtyTemplates[k.val]?.getD (0,∅,∅)).2.2

def badFamilies : List (List (Finset (Fin 16))) :=
  [[{1, 2, 8, 9, 10, 13}, {1, 6, 8, 9, 10, 11, 13, 14}], [{1, 2, 8, 9, 10, 13}, {2, 5, 7, 8, 9, 10, 12, 13}], [{2, 5, 7, 8, 9, 10, 12, 13}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}], [{1, 6, 8, 9, 10, 11, 13, 14}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}]]

def badList (k : Fin 4) : List (Finset (Fin 16)) := badFamilies[k.val]?.getD []

def badFamily (k : Fin 4) : Finset (Finset (Fin 16)) := (badList k).toFinset

def witnesses : List (List (Finset (Fin 16))) :=
  [[{1, 2, 8, 9, 10, 13}, ∅, {1, 6, 8, 9, 10, 11, 13, 14}, {1, 2, 8, 9, 10, 13}, {1, 2, 8, 9, 10, 13}], [{1, 2, 8, 9, 10, 13}, {2, 5, 7, 8, 9, 10, 12, 13}, ∅, {1, 2, 8, 9, 10, 13}, {1, 2, 8, 9, 10, 13}], [{2, 5, 7, 8, 9, 10, 12, 13}, ∅, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, {2, 5, 7, 8, 9, 10, 12, 13}, {2, 5, 7, 8, 9, 10, 12, 13}], [{1, 6, 8, 9, 10, 11, 13, 14}, {5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, ∅, {1, 6, 8, 9, 10, 11, 13, 14}, {1, 6, 8, 9, 10, 11, 13, 14}]]

def witness (k : Fin 4) (j : Fin 5) : Finset (Fin 16) :=
  ((witnesses[k.val]?.getD [])[j.val]?).getD ∅

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bad_card : ∀ k : Fin 4, (badFamily k).card = 2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem bad_check : ∀ k : Fin 4, (badList k).all (fun U => decide
    (U ∈ family ∧ (∃ u ∈ badLeft k, u ∈ U) ∧ (∃ v ∈ badRight k, v ∈ U))) = true := by
  decide +kernel

theorem dirty_family_check : ∀ k : Fin 4,
    (badFamily k).card = 2 ∧ badFamily k ⊆ family ∧
    ∀ U ∈ badFamily k, (∃ u ∈ badLeft k, u ∈ U) ∧ (∃ v ∈ badRight k, v ∈ U) := by
  intro k
  have data : ∀ U ∈ badFamily k, U ∈ family ∧
      (∃ u ∈ badLeft k, u ∈ U) ∧ (∃ v ∈ badRight k, v ∈ U) := by
    intro U hU
    have hlist : U ∈ badList k := by simpa [badFamily] using hU
    exact decide_eq_true_eq.mp (List.all_eq_true.mp (bad_check k) U hlist)
  exact ⟨bad_card k,fun U hU => (data U hU).1,fun U hU => (data U hU).2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem other_owner_witness : ∀ (k : Fin 4) (j : Fin 5),
    (Fin.castAdd 11 j : Fin 16) ≠ badOwner k →
    witness k j ∈ badFamily k ∧ Fin.castAdd 11 j ∉ witness k j ∧
      ∃ l : Fin 16, (Fin.castAdd 11 j,l) ∈ edgePairs ∧ l ∈ witness k j := by decide +kernel

def points : Finset (Fin 16) := {0,1,2,3,4}

def pointSubsets : List (Finset (Fin 16)) :=
  [∅, {0}, {1}, {0, 1}, {2}, {0, 2}, {1, 2}, {0, 1, 2}, {3}, {0, 3}, {1, 3}, {0, 1, 3}, {2, 3}, {0, 2, 3}, {1, 2, 3}, {0, 1, 2, 3}, {4}, {0, 4}, {1, 4}, {0, 1, 4}, {2, 4}, {0, 2, 4}, {1, 2, 4}, {0, 1, 2, 4}, {3, 4}, {0, 3, 4}, {1, 3, 4}, {0, 1, 3, 4}, {2, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}, {0, 1, 2, 3, 4}]

def canonical (P : Finset (Fin 16)) : Finset (Fin 16) :=
  P ∪ (Finset.univ \ points).filter (fun l => ∀ p ∈ P, (p,l) ∉ edgePairs)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem point_subsets_complete : pointSubsets.toFinset = points.powerset := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem cover_check : pointSubsets.all (fun P => negativeList.any
    (fun V => decide (canonical P ⊆ V))) = true := by decide +kernel

theorem independent_cover (U : Finset (Fin 16)) (hU : ¬hasEdge U) :
    ∃ V ∈ family, U ⊆ V := by
  let P := U ∩ points
  have hP : P ∈ pointSubsets := by
    have hp : P ∈ points.powerset := Finset.mem_powerset.mpr (Finset.inter_subset_right)
    rw [← point_subsets_complete] at hp
    simpa using hp
  have hc := List.all_eq_true.mp cover_check P hP
  obtain ⟨V,hV,hPV⟩ := List.any_eq_true.mp hc
  refine ⟨V,?_,?_⟩
  · simpa [family] using hV
  · apply Finset.Subset.trans (s₂ := canonical P) ?_ (decide_eq_true_eq.mp hPV)
    intro v hv
    by_cases hp : v ∈ points
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hv,hp⟩)
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hp⟩,?_⟩
      intro p hpin hedge
      exact hU ⟨(p,v),hedge,(Finset.mem_inter.mp hpin).1,hv⟩

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerNegatives

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerBridge

theorem edges_agree : FiveOwnerRectangles.edgePairs = FiveOwnerNegatives.edgePairs := rfl

theorem allowed_agree (u v : Fin 16) :
    FiveOwnerRectangles.allowed u v ↔ FiveOwnerNegatives.allowed u v := Iff.rfl

theorem dirty_index (L R : Finset (Fin 16))
    (h : (L, R) ∈ FiveOwnerRectangles.dirtyShapes) :
    ∃ t : Fin 4, L = FiveOwnerNegatives.badLeft t ∧ R = FiveOwnerNegatives.badRight t := by
  simp only [FiveOwnerRectangles.dirtyShapes, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h
  · exact ⟨0, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · exact ⟨1, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · exact ⟨2, congrArg Prod.fst h, congrArg Prod.snd h⟩
  · exact ⟨3, congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem ordinary_covered : ∀ p ∈ FiveOwnerRectangles.points,
    FiveOwnerRectangles.covered {p} (FiveOwnerRectangles.neighbors p) =
      FiveOwnerRectangles.ownerEdges p := by
  decide +kernel

theorem dirty_covered : ∀ t : Fin 4,
    FiveOwnerRectangles.covered (FiveOwnerNegatives.badLeft t) (FiveOwnerNegatives.badRight t) =
      FiveOwnerRectangles.ownerEdges (FiveOwnerNegatives.badOwner t) := by
  decide +kernel

theorem point_index : ∀ p ∈ FiveOwnerRectangles.points,
    ∃ j : Fin 5, Fin.castAdd 11 j = p := by
  decide +kernel

theorem dirty_owner_point : ∀ t : Fin 4,
    FiveOwnerNegatives.badOwner t ∈ FiveOwnerRectangles.points := by
  decide +kernel

theorem dirty_has_edge : ∀ t : Fin 4,
    ∃ l : Fin 16, (FiveOwnerNegatives.badOwner t, l) ∈ FiveOwnerNegatives.edgePairs := by
  decide +kernel

theorem ordinary_hit_edge (U L R : Finset (Fin 16))
    (h : FiveOwnerRectangles.Ordinary L R)
    (hL : ∃ u ∈ L, u ∈ U) (hR : ∃ v ∈ R, v ∈ U) :
    FiveOwnerNegatives.hasEdge U := by
  obtain ⟨p, hp, rfl, rfl⟩ := h
  obtain ⟨u, hu, huU⟩ := hL
  have hup : u = p := Finset.mem_singleton.mp hu
  subst u
  obtain ⟨v, hv, hvU⟩ := hR
  refine ⟨(p, v), ?_, huU, hvU⟩
  exact (Finset.mem_filter.mp hv).2

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerBridge
