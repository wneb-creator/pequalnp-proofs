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


namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerBudget

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Extracted from the generic local argument in accepted R-meta-5060-52.
-- This theorem concerns AndCountCircuit; no conversion or gate-count preservation
-- for a different circuit representation is asserted here.

theorem sideEq {n k} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (v : Fin k → Bool) :
    sideTrue U B F i v = decide ((∃ u ∈ B, u ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl

theorem outEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = decide ((∃ u ∈ C.outVars, u ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := rfl

theorem fuelEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (a : Nat) (i : Fin C.size) :
    C.gateValFuel U (a+1) i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U a) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U a)) := rfl

def wing {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) (b : Bool) :=
  sideTrue U (if b then C.rightVars i else C.leftVars i)
    (if b then C.rightGates i else C.leftGates i) i (C.gateVal U)

theorem stable {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (a b : Nat) (ha : i.val < a) (hb : i.val < b) :
    C.gateValFuel U a i = C.gateValFuel U b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      have eq (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
          sideTrue U B F i (C.gateValFuel U a) = sideTrue U B F i (C.gateValFuel U b) := by
        rw [sideEq,sideEq]
        congr 1
        apply propext
        constructor <;> rintro (raw | ⟨j,hj,lt,val⟩)
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h ▸ val⟩
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h.symm ▸ val⟩
      rw [fuelEq,fuelEq,eq,eq]

theorem value {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (wing C U i false && wing C U i true) :=
  stable C U i C.size (C.size+1) i.isLt (by omega)

theorem unionChoice {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (q : Fin C.size → Bool)
    (goodU : ∀ i, wing C U i (q i) = C.gateVal U i)
    (goodV : ∀ i, wing C V i (q i) = C.gateVal V i) :
    C.eval (U ∪ V) = true → C.eval U = true ∨ C.eval V = true := by
  have gates (d : Nat) : ∀ i : Fin C.size, C.gateValFuel (U ∪ V) d i = true →
      C.gateVal U i = true ∨ C.gateVal V i = true := by
    induction d with
    | zero => intro i h; cases h
    | succ d ih =>
      intro i h
      have both := Bool.and_eq_true_iff.mp h
      have pick : sideTrue (U ∪ V) (if q i then C.rightVars i else C.leftVars i)
          (if q i then C.rightGates i else C.leftGates i) i (C.gateValFuel (U ∪ V) d) = true := by
        cases q i
        · exact both.1
        · exact both.2
      rw [← goodU i, ← goodV i]
      simp only [wing,sideEq,decide_eq_true_eq] at pick ⊢
      rcases pick with ⟨v,hv,hmem⟩ | ⟨j,hj,hlt,on⟩
      · rcases Finset.mem_union.mp hmem with h | h
        · exact Or.inl (Or.inl ⟨v,hv,h⟩)
        · exact Or.inr (Or.inl ⟨v,hv,h⟩)
      · rcases ih j on with h | h
        · exact Or.inl (Or.inr ⟨j,hj,hlt,h⟩)
        · exact Or.inr (Or.inr ⟨j,hj,hlt,h⟩)
  simp only [outEq,decide_eq_true_eq]
  rintro (⟨v,hv,vhit⟩|⟨i,hi,hit⟩)
  · rcases Finset.mem_union.mp vhit with h | h
    · exact Or.inl (Or.inl ⟨v,hv,h⟩)
    · exact Or.inr (Or.inl ⟨v,hv,h⟩)
  · rcases gates C.size i hit with h | h
    · exact Or.inl (Or.inr ⟨i,hi,h⟩)
    · exact Or.inr (Or.inr ⟨i,hi,h⟩)

def free {n} (C : AndCountCircuit n) (U : Finset (Fin n)) : Finset (Fin C.size) :=
  Finset.univ.filter fun i => wing C U i false = wing C U i true

def encode {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size)) :
    Fin C.size → Bool := fun i => if i ∈ free C U then decide (i ∈ s) else wing C U i false

theorem good {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (s : Finset (Fin C.size))
    (i : Fin C.size) : wing C U i (encode C U s i) = C.gateVal U i := by
  rw [value]
  simp only [encode,free,Finset.mem_filter,Finset.mem_univ,true_and]
  cases h : wing C U i false <;> cases h' : wing C U i true <;> by_cases hs : i ∈ s <;> simp [h,h',hs]

theorem packing {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (neg : ∀ U ∈ F, C.eval U = false)
    (pos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) :
    (∑ U ∈ F, 2 ^ (free C U).card) ≤ 2 ^ C.size := by
  classical
  let cubes := fun U => (free C U).powerset.image (encode C U)
  have card (U : Finset (Fin n)) : (cubes U).card = 2^(free C U).card := by
    unfold cubes
    rw [Finset.card_image_iff.mpr ?_, Finset.card_powerset]
    intro s hs t ht eq
    have ssub := Finset.mem_powerset.mp hs
    have tsub := Finset.mem_powerset.mp ht
    ext i
    by_cases hi : i ∈ free C U
    · have he := congrFun eq i
      simpa only [encode,ite_eq_left hi,decide_eq_decide] using he
    · exact iff_of_false (fun h => hi (ssub h)) (fun h => hi (tsub h))
  have dis : (F : Set (Finset (Fin n))).PairwiseDisjoint cubes := by
    intro U hu V hv ne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hq
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hq'
    have both := unionChoice C U V q (hs ▸ good C U s) (ht ▸ good C V t) (pos U hu V hv ne)
    simp only [neg U hu,neg V hv, Bool.false_eq_true,or_self] at both
  calc
    _ = ∑ U ∈ F, (cubes U).card := by simp_rw [card]
    _ = (F.biUnion cubes).card := (Finset.card_biUnion dis).symm
    _ ≤ Fintype.card (Fin C.size → Bool) := Finset.card_le_univ _
    _ = _ := by simp


theorem weighted_slack_two {ι : Type} [DecidableEq ι]
    (S : Finset ι) (w : ι → ℕ) (h : (∑ s ∈ S, 2 ^ w s) ≤ S.card + 2) :
    (∀ s ∈ S, w s ≤ 1) ∧ (∑ s ∈ S, w s) ≤ 2 := by
  constructor
  · intro s hs
    have hc : (S.erase s).card + 1 = S.card := by
      simpa using Finset.sum_erase_add S (fun _ => (1 : ℕ)) hs
    have he := Finset.sum_erase_add S (fun t => 2 ^ w t) hs
    have hl : (S.erase s).card ≤ ∑ t ∈ S.erase s, 2 ^ w t := by
      calc
        _ = ∑ _t ∈ S.erase s, (1 : ℕ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun t _ => Nat.one_le_two_pow
    have hp : 2 ^ w s ≤ 3 := by omega
    have hw : w s < 2 ^ w s := Nat.lt_two_pow_self
    have hwle : w s ≤ 2 := by omega
    by_contra hn
    have hw2 : w s = 2 := by omega
    norm_num [hw2] at hp
  · have hl : S.card + (∑ s ∈ S, w s) ≤ ∑ s ∈ S, 2 ^ w s := by
      calc
        _ = ∑ s ∈ S, (1 + w s) := by simp [Finset.sum_add_distrib]
        _ ≤ _ := Finset.sum_le_sum fun s _ => by
          have hw : w s < 2 ^ w s := Nat.lt_two_pow_self
          omega
    omega

theorem side_mono {n k} (U V B : Finset (Fin n)) (G : Finset (Fin k))
    (i : Fin k) (f g : Fin k → Bool) (hUV : U ⊆ V)
    (hfg : ∀ j, f j = true → g j = true) :
    sideTrue U B G i f = true → sideTrue V B G i g = true := by
  simp only [sideEq, decide_eq_true_eq]
  rintro (⟨u,hu,hin⟩ | ⟨j,hj,hlt,hon⟩)
  · exact Or.inl ⟨u,hu,hUV hin⟩
  · exact Or.inr ⟨j,hj,hlt,hfg j hon⟩

theorem fuel_mono {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (hUV : U ⊆ V) :
    ∀ d (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero => intro i h; cases h
  | succ d ih =>
    intro i h
    rw [fuelEq] at h ⊢
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
    apply Bool.and_eq_true_iff.mpr
    exact ⟨side_mono U V _ _ i _ _ hUV ih hl, side_mono U V _ _ i _ _ hUV ih hr⟩

theorem gate_mono {n} (C : AndCountCircuit n) (U V : Finset (Fin n)) (hUV : U ⊆ V)
    (i : Fin C.size) : C.gateVal U i = true → C.gateVal V i = true :=
  fuel_mono C U V hUV C.size i

theorem active_mem_free {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (h : C.gateVal U i = true) : i ∈ free C U := by
  rw [value] at h
  obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.trans hr.symm⟩

theorem thirty_family_budget {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hcard : F.card = 30) (hsize : C.size ≤ 5)
    (hneg : ∀ U ∈ F, C.eval U = false)
    (hpos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true) :
    (∑ U ∈ F, (free C U).card) ≤ 2 := by
  have h := packing C F hneg hpos
  have hp : 2 ^ C.size ≤ 32 := by
    calc
      _ ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hsize
      _ = 32 := rfl
  exact (weighted_slack_two F (fun U => (free C U).card) (by omega)).2

theorem active_supersets_bound {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hbudget : (∑ V ∈ F, (free C V).card) ≤ 2)
    (U : Finset (Fin n)) (i : Fin C.size) (hon : C.gateVal U i = true) :
    (F.filter fun V => U ⊆ V).card ≤ 2 := by
  let A := F.filter fun V => U ⊆ V
  have hactive : ∀ V ∈ A, i ∈ free C V := by
    intro V hV
    exact active_mem_free C V i (gate_mono C U V (Finset.mem_filter.mp hV).2 i hon)
  have hlow : A.card ≤ ∑ V ∈ A, (free C V).card := by
    calc
      _ = ∑ _V ∈ A, (1 : ℕ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun V hV =>
        Nat.succ_le_iff.mpr (Finset.card_pos.mpr ⟨i,hactive V hV⟩)
  have hsub : (∑ V ∈ A, (free C V).card) ≤ ∑ V ∈ F, (free C V).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)
  change A.card ≤ 2
  omega

theorem false_of_three_supersets {n} (C : AndCountCircuit n) (F : Finset (Finset (Fin n)))
    (hbudget : (∑ V ∈ F, (free C V).card) ≤ 2)
    (U : Finset (Fin n)) (hcount : 3 ≤ (F.filter fun V => U ⊆ V).card)
    (i : Fin C.size) : C.gateVal U i = false := by
  cases hv : C.gateVal U i
  · rfl
  · have h := active_supersets_bound C F hbudget U i hv
    omega

theorem two_events_exhaust {ι κ : Type} [DecidableEq ι] [DecidableEq κ]
    (F A : Finset ι) (events : ι → Finset κ) (k : κ)
    (hcard : A.card = 2) (hsub : A ⊆ F)
    (hbase : ∀ a ∈ A, k ∈ events a)
    (hbudget : (∑ a ∈ F, (events a).card) ≤ 2) :
    ∀ a ∈ F, ∀ j ∈ events a, j = k := by
  let cells : Finset (Sigma fun _ : ι => κ) := F.sigma events
  let base : Finset (Sigma fun _ : ι => κ) := A.image fun a => ⟨a,k⟩
  have hbcard : base.card = 2 := by
    change (A.image fun a => (⟨a,k⟩ : Sigma fun _ : ι => κ)).card = 2
    rw [Finset.card_image_iff.mpr (by
      intro a ha b hb he
      exact congrArg (fun x : Sigma fun _ : ι => κ => x.1) he)]
    exact hcard
  have hbcells : base ⊆ cells := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_sigma.mpr ⟨hsub ha,hbase a ha⟩
  have hccard : cells.card ≤ 2 := by simpa [cells, Finset.card_sigma] using hbudget
  intro a ha j hj
  by_contra hne
  let cell : Sigma fun _ : ι => κ := ⟨a,j⟩
  have hcell : cell ∈ cells := Finset.mem_sigma.mpr ⟨ha,hj⟩
  have hnot : cell ∉ base := by
    intro hc
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hc
    have he' := congrArg (fun x : Sigma fun _ : ι => κ => x.2) he
    exact hne he'.symm
  have hins : insert cell base ⊆ cells := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hb
    · exact hcell
    · exact hbcells hb
  have hcount := Finset.card_le_card hins
  rw [Finset.card_insert_of_notMem hnot, hbcard] at hcount
  omega

theorem other_gate_false_after_two_bad_inputs {n} (C : AndCountCircuit n)
    (F A : Finset (Finset (Fin n))) (k : Fin C.size)
    (hcard : A.card = 2) (hsub : A ⊆ F)
    (hbase : ∀ U ∈ A, C.gateVal U k = true)
    (hbudget : (∑ U ∈ F, (free C U).card) ≤ 2) :
    ∀ U ∈ F, ∀ i : Fin C.size, i ≠ k → C.gateVal U i = false := by
  have he := two_events_exhaust F A (free C) k hcard hsub
    (fun U hU => active_mem_free C U k (hbase U hU)) hbudget
  intro U hU i hne
  cases hv : C.gateVal U i
  · rfl
  · exact False.elim (hne (he U hU i (active_mem_free C U i hv)))

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerBudget


namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerPropagation

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Extracted from the generic local argument in accepted R-meta-5060-52.
-- This theorem concerns AndCountCircuit; no conversion or gate-count preservation
-- for a different circuit representation is asserted here.

theorem sideEq {n k} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k) (v : Fin k → Bool) :
    sideTrue U B F i v = decide ((∃ u ∈ B, u ∈ U) ∨ ∃ j ∈ F, j < i ∧ v j = true) := rfl

theorem outEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    C.eval U = decide ((∃ u ∈ C.outVars, u ∈ U) ∨ ∃ j ∈ C.outGates, C.gateVal U j = true) := rfl

theorem fuelEq {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (a : Nat) (i : Fin C.size) :
    C.gateValFuel U (a+1) i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateValFuel U a) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateValFuel U a)) := rfl

def wing {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) (b : Bool) :=
  sideTrue U (if b then C.rightVars i else C.leftVars i)
    (if b then C.rightGates i else C.leftGates i) i (C.gateVal U)

theorem stable {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size)
    (a b : Nat) (ha : i.val < a) (hb : i.val < b) :
    C.gateValFuel U a i = C.gateValFuel U b i := by
  induction a generalizing i b with
  | zero => omega
  | succ a ih =>
    cases b with
    | zero => omega
    | succ b =>
      have eq (B : Finset (Fin n)) (F : Finset (Fin C.size)) :
          sideTrue U B F i (C.gateValFuel U a) = sideTrue U B F i (C.gateValFuel U b) := by
        rw [sideEq,sideEq]
        congr 1
        apply propext
        constructor <;> rintro (raw | ⟨j,hj,lt,val⟩)
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h ▸ val⟩
        · exact Or.inl raw
        · have h := ih j b (by change j.val < i.val at lt; omega) (by change j.val < i.val at lt; omega)
          exact Or.inr ⟨j,hj,lt,h.symm ▸ val⟩
      rw [fuelEq,fuelEq,eq,eq]

theorem value {n} (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) :
    C.gateVal U i = (wing C U i false && wing C U i true) :=
  stable C U i C.size (C.size+1) i.isLt (by omega)


def sideVars {n} (C : AndCountCircuit n) (i : Fin C.size) (b : Bool) :=
  if b then C.rightVars i else C.leftVars i

def sideGates {n} (C : AndCountCircuit n) (i : Fin C.size) (b : Bool) :=
  if b then C.rightGates i else C.leftGates i

def rawHit {n} (U B : Finset (Fin n)) : Prop := ∃ u ∈ B, u ∈ U

theorem wing_parts {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (b : Bool) :
    wing C U i b = true ↔ rawHit U (sideVars C i b) ∨
      ∃ j ∈ sideGates C i b, j < i ∧ C.gateVal U j = true := by
  simp only [wing, sideEq, decide_eq_true_eq, rawHit, sideVars, sideGates]

theorem active_wing {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (h : C.gateVal U i = true) (b : Bool) : wing C U i b = true := by
  rw [value] at h
  have both := Bool.and_eq_true_iff.mp h
  cases b
  · exact both.1
  · exact both.2

theorem active_of_raw {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) (hl : rawHit U (C.leftVars i)) (hr : rawHit U (C.rightVars i)) :
    C.gateVal U i = true := by
  rw [value]
  apply Bool.and_eq_true_iff.mpr
  exact ⟨(wing_parts C U i false).mpr (Or.inl hl),
    (wing_parts C U i true).mpr (Or.inl hr)⟩

theorem no_out_vars_of_rejected_singletons {n} (C : AndCountCircuit n)
    (h : ∀ v : Fin n, C.eval {v} = false) : C.outVars = ∅ := by
  apply Finset.ext
  intro v
  constructor
  · intro hv
    have hon : C.eval {v} = true := by
      rw [outEq]
      apply decide_eq_true_eq.mpr
      exact Or.inl ⟨v,hv,by simp⟩
    rw [h v] at hon
    cases hon
  · intro hv
    simp at hv

theorem sides_disjoint_of_singletons {n} (C : AndCountCircuit n)
    (h : ∀ (i : Fin C.size) (v : Fin n), C.gateVal {v} i = false)
    (i : Fin C.size) : Disjoint (C.leftVars i) (C.rightVars i) := by
  apply Finset.disjoint_left.mpr
  intro v hl hr
  have hon := active_of_raw C {v} i ⟨v,hl,by simp⟩ ⟨v,hr,by simp⟩
  rw [h i v] at hon
  cases hon

theorem first_active_raw {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (h : ∃ i : Fin C.size, C.gateVal U i = true) :
    ∃ i : Fin C.size, C.gateVal U i = true ∧
      (∀ j, j < i → C.gateVal U j = false) ∧
      rawHit U (C.leftVars i) ∧ rawHit U (C.rightVars i) := by
  let A := Finset.univ.filter fun i => C.gateVal U i = true
  have hA : A.Nonempty := by
    obtain ⟨i,hi⟩ := h
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let i := A.min' hA
  have hi : i ∈ A := Finset.min'_mem A hA
  have hon : C.gateVal U i = true := (Finset.mem_filter.mp hi).2
  have before : ∀ j, j < i → C.gateVal U j = false := by
    intro j hj
    cases hv : C.gateVal U j
    · rfl
    · have hjA : j ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
      have hmin : i ≤ j := Finset.min'_le A j hjA
      exact False.elim (not_lt_of_ge hmin hj)
  refine ⟨i,hon,before,?_,?_⟩
  · rcases (wing_parts C U i false).mp (active_wing C U i hon false) with raw | ⟨j,hj,lt,on⟩
    · exact raw
    · rw [before j lt] at on
      cases on
  · rcases (wing_parts C U i true).mp (active_wing C U i hon true) with raw | ⟨j,hj,lt,on⟩
    · exact raw
    · rw [before j lt] at on
      cases on

theorem pair_has_origin {n} (C : AndCountCircuit n) (u v : Fin n)
    (hout : C.outVars = ∅)
    (hsingle : ∀ (i : Fin C.size) (w : Fin n), C.gateVal {w} i = false)
    (hpair : C.eval {u,v} = true) :
    ∃ i : Fin C.size, (u ∈ C.leftVars i ∧ v ∈ C.rightVars i) ∨
      (v ∈ C.leftVars i ∧ u ∈ C.rightVars i) := by
  have hactive : ∃ i : Fin C.size, C.gateVal {u,v} i = true := by
    rw [outEq] at hpair
    have hp := decide_eq_true_eq.mp hpair
    rcases hp with ⟨w,hw,_⟩ | ⟨i,hi,hon⟩
    · simp [hout] at hw
    · exact ⟨i,hon⟩
  obtain ⟨i,hi,hbefore,⟨l,hl,hlU⟩,⟨r,hr,hrU⟩⟩ := first_active_raw C {u,v} hactive
  have hd := Finset.disjoint_left.mp (sides_disjoint_of_singletons C hsingle i)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hlU hrU
  refine ⟨i,?_⟩
  rcases hlU with rfl | rfl <;> rcases hrU with rfl | rfl
  · exact False.elim (hd hl hr)
  · exact Or.inl ⟨hl,hr⟩
  · exact Or.inr ⟨hl,hr⟩
  · exact False.elim (hd hl hr)

-- A rejected input prevents a true source from entering a wing whose opposite raw wing is true.
theorem rejected_forbids_source {n} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i k : Fin C.size) (b : Bool) (hk : C.gateVal U k = true)
    (hi : C.gateVal U i = false) (hlt : k < i)
    (hraw : rawHit U (sideVars C i (!b))) : k ∉ sideGates C i b := by
  intro hin
  have hside : wing C U i b = true :=
    (wing_parts C U i b).mpr (Or.inr ⟨k,hin,hlt,hk⟩)
  have hother : wing C U i (!b) = true :=
    (wing_parts C U i (!b)).mpr (Or.inl hraw)
  have hon : C.gateVal U i = true := by
    rw [value]
    apply Bool.and_eq_true_iff.mpr
    cases b
    · exact ⟨hside,hother⟩
    · exact ⟨hother,hside⟩
  rw [hi] at hon
  cases hon

-- If all other point wings have no active raw input and exclude the chosen gate,
-- no other gate can become the first active successor of that gate.
theorem only_selected_active {n} (C : AndCountCircuit n) (P : Finset (Fin n))
    (k : Fin C.size) (pointSide : Fin C.size → Bool)
    (hraw : ∀ j, j ≠ k → ¬rawHit P (sideVars C j (pointSide j)))
    (hexclude : ∀ j, k < j → k ∉ sideGates C j (pointSide j)) :
    ∀ j, j ≠ k → C.gateVal P j = false := by
  have aux : ∀ t : ℕ, ∀ j : Fin C.size, j.val = t → j ≠ k → C.gateVal P j = false := by
    intro t
    induction t using Nat.strong_induction_on with
    | ind t ih =>
      intro j hj hne
      cases hv : C.gateVal P j
      · rfl
      · have hp := (wing_parts C P j (pointSide j)).mp (active_wing C P j hv (pointSide j))
        rcases hp with raw | ⟨s,hs,hlt,hsval⟩
        · exact False.elim (hraw j hne raw)
        · by_cases hsk : s = k
          · subst s
            exact False.elim (hexclude j hlt hs)
          · have hslt : s.val < t := by change s.val < j.val at hlt; omega
            have hzero := ih s.val hslt s rfl hsk
            rw [hzero] at hsval
            cases hsval
  intro j hne
  exact aux j.val j rfl hne

theorem dirty_source_cannot_compute {n} (C : AndCountCircuit n)
    (P N : Finset (Fin n)) (k : Fin C.size) (pointSide : Fin C.size → Bool)
    (hout : C.outVars = ∅)
    (hraw : ∀ j, j ≠ k → ¬rawHit P (sideVars C j (pointSide j)))
    (hexclude : ∀ j, k < j → k ∉ sideGates C j (pointSide j))
    (hk : C.gateVal N k = true) (hneg : C.eval N = false) (hpos : C.eval P = true) : False := by
  have only := only_selected_active C P k pointSide hraw hexclude
  rw [outEq] at hpos
  have hp := decide_eq_true_eq.mp hpos
  rcases hp with ⟨v,hv,_⟩ | ⟨i,hi,hon⟩
  · simp [hout] at hv
  · have hik : i = k := by
      by_contra hne
      rw [only i hne] at hon
      cases hon
    subst i
    have hwrong : C.eval N = true := by
      rw [outEq]
      exact decide_eq_true_eq.mpr (Or.inr ⟨k,hi,hk⟩)
    rw [hneg] at hwrong
    cases hwrong

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerPropagation


namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerCoverage

theorem twenty_cover_five {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (E : Finset α) (B : ι → Finset α)
    (hi : I.card = 5) (he : E.card = 20)
    (hb : ∀ i ∈ I, (B i).card ≤ 4)
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i) :
    ∀ i ∈ I, (B i).card = 4 := by
  have hsub : E ⊆ I.biUnion B := by
    intro e he
    obtain ⟨i,hi,hb⟩ := hcover e he
    exact Finset.mem_biUnion.mpr ⟨i,hi,hb⟩
  have htotal : 20 ≤ ∑ i ∈ I, (B i).card := by
    have h1 := Finset.card_le_card hsub
    have h2 : (I.biUnion B).card ≤ ∑ i ∈ I, (B i).card := Finset.card_biUnion_le
    omega
  intro i him
  have hc : (I.erase i).card = 4 := by
    have h := Finset.sum_erase_add I (fun _ => (1 : ℕ)) him
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    omega
  have hrest : (∑ j ∈ I.erase i, (B j).card) ≤ 16 := by
    calc
      _ ≤ ∑ _j ∈ I.erase i, (4 : ℕ) := Finset.sum_le_sum fun j hj =>
        hb j (Finset.mem_of_mem_erase hj)
      _ = 16 := by simp [hc]
  have hs := Finset.sum_erase_add I (fun j => (B j).card) him
  have hu := hb i him
  omega

theorem twenty_cover_distinct {ι α : Type} [DecidableEq ι] [DecidableEq α]
    (I : Finset ι) (E : Finset α) (B : ι → Finset α)
    (hi : I.card = 5) (he : E.card = 20)
    (hb : ∀ i ∈ I, (B i).card ≤ 4)
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i) :
    ∀ i ∈ I, ∀ j ∈ I, i ≠ j → B i ≠ B j := by
  intro i him j hjm hne heq
  have hsub : E ⊆ (I.erase j).biUnion B := by
    intro e hem
    obtain ⟨k,hkm,hek⟩ := hcover e hem
    by_cases hkj : k = j
    · subst k
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_erase.mpr ⟨hne,him⟩,heq.symm ▸ hek⟩
    · exact Finset.mem_biUnion.mpr ⟨k,Finset.mem_erase.mpr ⟨hkj,hkm⟩,hek⟩
  have hc : (I.erase j).card = 4 := by
    have h := Finset.sum_erase_add I (fun _ => (1 : ℕ)) hjm
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
    omega
  have hs : (∑ k ∈ I.erase j, (B k).card) ≤ 16 := by
    calc
      _ ≤ ∑ _k ∈ I.erase j, (4 : ℕ) := Finset.sum_le_sum fun k hk =>
        hb k (Finset.mem_of_mem_erase hk)
      _ = 16 := by simp [hc]
  have h1 := Finset.card_le_card hsub
  have h2 : ((I.erase j).biUnion B).card ≤ ∑ k ∈ I.erase j, (B k).card :=
    Finset.card_biUnion_le
  omega

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerCoverage


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

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerClean

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit
open PEqualNP.Outside.L_meta_650_aux

theorem singleton_no_edge : ∀ v : Fin 16, ¬FiveOwnerNegatives.hasEdge {v} := by decide +kernel

theorem template_active (C : AndCountCircuit 16) (i : Fin C.size) (t : Fin 4) (b : Bool)
    (hl : FiveOwnerPropagation.sideVars C i b = FiveOwnerNegatives.badLeft t)
    (hr : FiveOwnerPropagation.sideVars C i (!b) = FiveOwnerNegatives.badRight t) :
    ∀ U ∈ FiveOwnerNegatives.badFamily t, C.gateVal U i = true := by
  intro U hU
  obtain ⟨hL,hR⟩ := (FiveOwnerNegatives.dirty_family_check t).2.2 U hU
  have hleft : FiveOwnerPropagation.wing C U i b = true := by
    apply (FiveOwnerPropagation.wing_parts C U i b).mpr
    apply Or.inl
    change ∃ u ∈ FiveOwnerPropagation.sideVars C i b, u ∈ U
    rw [hl]
    exact hL
  have hright : FiveOwnerPropagation.wing C U i (!b) = true := by
    apply (FiveOwnerPropagation.wing_parts C U i (!b)).mpr
    apply Or.inl
    change ∃ u ∈ FiveOwnerPropagation.sideVars C i (!b), u ∈ U
    rw [hr]
    exact hR
  rw [FiveOwnerPropagation.value]
  apply Bool.and_eq_true_iff.mpr
  cases b
  · exact ⟨hleft,hright⟩
  · exact ⟨hright,hleft⟩

theorem classify_gate (C : AndCountCircuit 16) (i : Fin C.size)
    (ha : FiveOwnerRectangles.AllAllowed (C.leftVars i) (C.rightVars i))
    (hc : 4 ≤ (FiveOwnerRectangles.covered (C.leftVars i) (C.rightVars i)).card) :
    (∃ p ∈ FiveOwnerRectangles.points, ∃ b : Bool,
      FiveOwnerPropagation.sideVars C i b = {p} ∧
      FiveOwnerPropagation.sideVars C i (!b) = FiveOwnerRectangles.neighbors p) ∨
    (∃ t : Fin 4, ∃ b : Bool,
      FiveOwnerPropagation.sideVars C i b = FiveOwnerNegatives.badLeft t ∧
      FiveOwnerPropagation.sideVars C i (!b) = FiveOwnerNegatives.badRight t) := by
  rcases FiveOwnerRectangles.point_side (C.leftVars i) (C.rightVars i) ha hc with
    ho | ho | hd | hd
  · obtain ⟨p,hp,hl,hr⟩ := ho
    exact Or.inl ⟨p,hp,false,hl,hr⟩
  · obtain ⟨p,hp,hl,hr⟩ := ho
    exact Or.inl ⟨p,hp,true,hl,hr⟩
  · obtain ⟨t,hl,hr⟩ := FiveOwnerBridge.dirty_index _ _ hd
    exact Or.inr ⟨t,false,hl,hr⟩
  · obtain ⟨t,hl,hr⟩ := FiveOwnerBridge.dirty_index _ _ hd
    exact Or.inr ⟨t,true,hl,hr⟩

set_option maxHeartbeats 4000000 in
theorem five_and_clean (C : AndCountCircuit 16) (hsize : C.size ≤ 5)
    (hcorrect : ∀ U : Finset (Fin 16), C.eval U = true ↔ FiveOwnerNegatives.hasEdge U) :
    ∀ (i : Fin C.size) (U : Finset (Fin 16)), ¬FiveOwnerNegatives.hasEdge U →
      C.gateVal U i = false := by
  classical
  let F := FiveOwnerNegatives.family
  let E := FiveOwnerRectangles.edgePairs
  let B := fun i : Fin C.size => FiveOwnerRectangles.covered (C.leftVars i) (C.rightVars i)
  have hneg : ∀ U ∈ F, C.eval U = false := by
    intro U hU
    cases hv : C.eval U
    · rfl
    · exact False.elim (FiveOwnerNegatives.family_negative U hU ((hcorrect U).mp hv))
  have hpos : ∀ U ∈ F, ∀ V ∈ F, U ≠ V → C.eval (U ∪ V) = true :=
    fun U hU V hV hne => (hcorrect _).mpr (FiveOwnerNegatives.pair_positive U V hU hV hne)
  have hbudget := FiveOwnerBudget.thirty_family_budget C F FiveOwnerNegatives.family_card hsize hneg hpos
  have hsingle : ∀ (i : Fin C.size) (v : Fin 16), C.gateVal {v} i = false := by
    intro i v
    apply FiveOwnerBudget.false_of_three_supersets C F hbudget {v} ?_ i
    have hc : 4 ≤ (F.filter fun U => v ∈ U).card := FiveOwnerNegatives.singleton_count v
    simpa only [Finset.singleton_subset_iff] using (show 3 ≤ (F.filter fun U => v ∈ U).card by omega)
  have hout : C.outVars = ∅ := FiveOwnerPropagation.no_out_vars_of_rejected_singletons C (by
    intro v
    cases hv : C.eval {v}
    · rfl
    · exact False.elim (singleton_no_edge v ((hcorrect _).mp hv)))
  have hall : ∀ i, FiveOwnerRectangles.AllAllowed (C.leftVars i) (C.rightVars i) := by
    intro i u hu v hv
    change FiveOwnerNegatives.allowed u v
    by_contra hno
    have hc := FiveOwnerNegatives.forbidden_pair_count u v hno
    have hzero := FiveOwnerBudget.false_of_three_supersets C F hbudget {u,v}
      (by simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using hc) i
    have hon := FiveOwnerPropagation.active_of_raw C {u,v} i ⟨u,hu,by simp⟩ ⟨v,hv,by simp⟩
    rw [hzero] at hon
    cases hon
  have hsmall : ∀ i, (B i).card ≤ 4 := fun i => FiveOwnerRectangles.max_four _ _ (hall i)
  have hcover : ∀ e ∈ E, ∃ i ∈ (Finset.univ : Finset (Fin C.size)), e ∈ B i := by
    intro e he
    have hpair : C.eval {e.1,e.2} = true := (hcorrect _).mpr ⟨e,he,by simp,by simp⟩
    obtain ⟨i,hi⟩ := FiveOwnerPropagation.pair_has_origin C e.1 e.2 hout hsingle hpair
    exact ⟨i,Finset.mem_univ _,Finset.mem_filter.mpr ⟨he,hi.imp id And.symm⟩⟩
  have hsize_eq : C.size = 5 := by
    have hp := FiveOwnerBudget.packing C F hneg hpos
    have hlo : 30 ≤ ∑ U ∈ F, 2 ^ (FiveOwnerBudget.free C U).card := by
      calc
        _ = ∑ _U ∈ F, (1 : ℕ) := by simp [F, FiveOwnerNegatives.family_card]
        _ ≤ _ := Finset.sum_le_sum fun U _ => Nat.one_le_two_pow
    by_contra hne
    have hs4 : C.size ≤ 4 := by omega
    have hp4 : 2 ^ C.size ≤ 16 := by
      calc
        _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hs4
        _ = 16 := rfl
    omega
  have hI : (Finset.univ : Finset (Fin C.size)).card = 5 := by simp [hsize_eq]
  have hE : E.card = 20 := by decide +kernel
  have hfour : ∀ i, (B i).card = 4 := fun i =>
    FiveOwnerCoverage.twenty_cover_five Finset.univ E B hI hE (fun i _ => hsmall i) hcover i (Finset.mem_univ _)
  have hdistinct : ∀ i j, i ≠ j → B i ≠ B j := fun i j hne =>
    FiveOwnerCoverage.twenty_cover_distinct Finset.univ E B hI hE (fun i _ => hsmall i) hcover
      i (Finset.mem_univ _) j (Finset.mem_univ _) hne
  have side_covered : ∀ (i : Fin C.size) (b : Bool), B i = FiveOwnerRectangles.covered
      (FiveOwnerPropagation.sideVars C i b) (FiveOwnerPropagation.sideVars C i (!b)) := by
    intro i b
    cases b
    · rfl
    · exact FiveOwnerRectangles.covered_swap _ _
  have family_clean : ∀ U ∈ F, ∀ i, C.gateVal U i = false := by
    intro U hU i
    cases hon : C.gateVal U i
    · rfl
    · obtain ⟨k,hkon,hbefore,hrawL,hrawR⟩ := FiveOwnerPropagation.first_active_raw C U ⟨i,hon⟩
      have hkclass := classify_gate C k (hall k) (by rw [hfour k])
      have hkdirty : ∃ t : Fin 4, ∃ b : Bool,
          FiveOwnerPropagation.sideVars C k b = FiveOwnerNegatives.badLeft t ∧
          FiveOwnerPropagation.sideVars C k (!b) = FiveOwnerNegatives.badRight t := by
        rcases hkclass with ⟨p,hp,b,hl,hr⟩ | hd
        · have hedge : FiveOwnerNegatives.hasEdge U := by
            cases b
            · exact FiveOwnerBridge.ordinary_hit_edge U _ _ ⟨p,hp,hl,hr⟩ hrawL hrawR
            · exact FiveOwnerBridge.ordinary_hit_edge U _ _ ⟨p,hp,hl,hr⟩ hrawR hrawL
          exact False.elim (FiveOwnerNegatives.family_negative U hU hedge)
        · exact hd
      obtain ⟨t,b,hkL,hkR⟩ := hkdirty
      have hbase := template_active C k t b hkL hkR
      have hothers := FiveOwnerBudget.other_gate_false_after_two_bad_inputs C F
        (FiveOwnerNegatives.badFamily t) k (FiveOwnerNegatives.bad_card t)
        (FiveOwnerNegatives.dirty_family_check t).2.1 hbase hbudget
      have hkcovered : B k = FiveOwnerRectangles.ownerEdges (FiveOwnerNegatives.badOwner t) := by
        rw [side_covered k b, hkL, hkR]
        exact FiveOwnerBridge.dirty_covered t
      have ordinary_other : ∀ j, j ≠ k → ∃ p ∈ FiveOwnerRectangles.points, ∃ c : Bool,
          p ≠ FiveOwnerNegatives.badOwner t ∧ FiveOwnerPropagation.sideVars C j c = {p} ∧
          FiveOwnerPropagation.sideVars C j (!c) = FiveOwnerRectangles.neighbors p := by
        intro j hj
        rcases classify_gate C j (hall j) (by rw [hfour j]) with ⟨p,hp,c,hl,hr⟩ | ⟨s,c,hl,hr⟩
        · refine ⟨p,hp,c,?_,hl,hr⟩
          intro hsame
          have hjcovered : B j = FiveOwnerRectangles.ownerEdges p := by
            rw [side_covered j c, hl, hr]
            exact FiveOwnerBridge.ordinary_covered p hp
          exact hdistinct j k hj (hjcovered.trans ((congrArg FiveOwnerRectangles.ownerEdges hsame).trans hkcovered.symm))
        · have hsne : (FiveOwnerNegatives.badFamily s).Nonempty := by
            apply Finset.card_pos.mp
            rw [FiveOwnerNegatives.bad_card s]
            decide
          obtain ⟨V,hV⟩ := hsne
          have hvon := template_active C j s c hl hr V hV
          have hvoff := hothers V ((FiveOwnerNegatives.dirty_family_check s).2.1 hV) j hj
          rw [hvoff] at hvon
          cases hvon
      have choice : ∀ j : Fin C.size, ∃ c : Bool, j ≠ k →
          ∃ p ∈ FiveOwnerRectangles.points, p ≠ FiveOwnerNegatives.badOwner t ∧
            FiveOwnerPropagation.sideVars C j c = {p} ∧
            FiveOwnerPropagation.sideVars C j (!c) = FiveOwnerRectangles.neighbors p := by
        intro j
        by_cases hj : j = k
        · exact ⟨false,fun h => False.elim (h hj)⟩
        · obtain ⟨p,hp,c,hne,hl,hr⟩ := ordinary_other j hj
          exact ⟨c,fun _ => ⟨p,hp,hne,hl,hr⟩⟩
      choose pointSide hside using choice
      obtain ⟨l,hel⟩ := FiveOwnerBridge.dirty_has_edge t
      have hline : l ∉ FiveOwnerRectangles.points := (FiveOwnerRectangles.edge_sides _ hel).2
      let P : Finset (Fin 16) := {FiveOwnerNegatives.badOwner t,l}
      have hraw : ∀ j, j ≠ k → ¬FiveOwnerPropagation.rawHit P
          (FiveOwnerPropagation.sideVars C j (pointSide j)) := by
        intro j hj
        obtain ⟨p,hp,hne,hl,hr⟩ := hside j hj
        change ¬ ∃ v ∈ FiveOwnerPropagation.sideVars C j (pointSide j), v ∈ P
        rw [hl]
        rintro ⟨v,hv,hvP⟩
        have heq : v = p := Finset.mem_singleton.mp hv
        subst v
        simp only [P, Finset.mem_insert, Finset.mem_singleton] at hvP
        rcases hvP with h | h
        · exact hne h
        · exact hline (h ▸ hp)
      have hexclude : ∀ j, k < j → k ∉ FiveOwnerPropagation.sideGates C j (pointSide j) := by
        intro j hkj
        have hj : j ≠ k := by intro h; subst j; exact (lt_irrefl k) hkj
        obtain ⟨p,hp,hne,hl,hr⟩ := hside j hj
        obtain ⟨pj,hpj⟩ := FiveOwnerBridge.point_index p hp
        have hw := FiveOwnerNegatives.other_owner_witness t pj (by rw [hpj]; exact hne)
        let V := FiveOwnerNegatives.witness t pj
        have hVF : V ∈ F := (FiveOwnerNegatives.dirty_family_check t).2.1 hw.1
        apply FiveOwnerPropagation.rejected_forbids_source C V j k (pointSide j)
          (hbase V hw.1) (hothers V hVF j hj) hkj
        change ∃ v ∈ FiveOwnerPropagation.sideVars C j (!(pointSide j)), v ∈ V
        rw [hr]
        obtain ⟨v,hev,hv⟩ := hw.2.2
        refine ⟨v,?_,hv⟩
        simp only [FiveOwnerRectangles.neighbors, Finset.mem_filter, Finset.mem_univ, true_and]
        change (p,v) ∈ FiveOwnerNegatives.edgePairs
        simpa only [hpj] using hev
      have htne : (FiveOwnerNegatives.badFamily t).Nonempty := by
        apply Finset.card_pos.mp
        rw [FiveOwnerNegatives.bad_card t]
        decide
      obtain ⟨N,hN⟩ := htne
      have hNF : N ∈ F := (FiveOwnerNegatives.dirty_family_check t).2.1 hN
      have hP : C.eval P = true := (hcorrect P).mpr ⟨(FiveOwnerNegatives.badOwner t,l),hel,by simp [P],by simp [P]⟩
      exact False.elim (FiveOwnerPropagation.dirty_source_cannot_compute C P N k pointSide
        hout hraw hexclude (hbase N hN) (hneg N hNF) hP)
  intro i U hU
  obtain ⟨V,hVF,hUV⟩ := FiveOwnerNegatives.independent_cover U hU
  cases hon : C.gateVal U i
  · rfl
  · have hvon := FiveOwnerBudget.gate_mono C U V hUV i hon
    rw [family_clean V hVF i] at hvon
    cases hvon

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerClean


namespace PEqualNP.Outside.L_meta_650_aux.TightConversion

open PEqualNP.CircuitLowerBounds

abbrev Rec (n : ℕ) := Finset (Fin n) × Finset ℕ × Finset (Fin n) × Finset ℕ
abbrev Form (n : ℕ) := Option (Finset (Fin n) × Finset ℕ)

def zeroF {n : ℕ} : Form n := some (∅, ∅)

def orF {n : ℕ} : List (Form n) → Form n
  | [] => some (∅, ∅)
  | f :: fs =>
    match f, orF fs with
    | none, _ => none
    | some _, none => none
    | some (a, b), some (c, d) => some (a ∪ c, b ∪ d)

structure St (n : ℕ) where
  fs : List (Form n)
  rs : List (Rec n)

def getF {n : ℕ} (s : St n) (i : ℕ) : Form n := s.fs.getD i zeroF

def andStep {n : ℕ} (s : St n) (fa fb : Form n) : St n :=
  match fa, fb with
  | none, f => ⟨s.fs ++ [f], s.rs⟩
  | some p, none => ⟨s.fs ++ [some p], s.rs⟩
  | some (va, ga), some (vb, gb) => ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [(va, ga, vb, gb)]⟩

def step {n : ℕ} (s : St n) (g : Gate) : St n :=
  match g.op, g.inputs with
  | GateOp.or, ins => ⟨s.fs ++ [orF (ins.map (getF s))], s.rs⟩
  | GateOp.and, [] => ⟨s.fs ++ [none], s.rs⟩
  | GateOp.and, [a] => ⟨s.fs ++ [getF s a], s.rs⟩
  | GateOp.and, a :: b :: _ => andStep s (getF s a) (getF s b)
  | _, _ => ⟨s.fs ++ [zeroF], s.rs⟩

def sv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (V : Finset (Fin n)) (G : Finset ℕ) : Bool :=
  decide (∃ v ∈ V, v ∈ U) || decide (∃ j ∈ G, vs.getD j false = true)

def rvStep {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (r : Rec n) : List Bool :=
  vs ++ [sv U vs r.1 r.2.1 && sv U vs r.2.2.1 r.2.2.2]

def rvals {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : List Bool := rs.foldl (rvStep U) []

def fv {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : Form n → Bool
  | none => true
  | some p => sv U vs p.1 p.2

theorem fv_orF {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) (fs : List (Form n)) :
    fv U vs (orF fs) = fs.any (fv U vs) := by
  induction fs with
  | nil => simp [orF, fv, sv]
  | cons f fs ih =>
    rcases f with _ | ⟨a, b⟩
    · simp [orF, fv]
    · rcases h : orF fs with _ | ⟨c, d⟩
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp [fv]
      · rw [h] at ih
        simp only [orF, h, List.any_cons]
        rw [← ih]
        simp only [fv, sv, Finset.mem_union, or_and_right, exists_or, Bool.decide_or]
        ac_rfl

theorem rv_pre {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ (vs : List Bool) (j : ℕ), j < vs.length → (rs.foldl (rvStep U) vs).getD j false = vs.getD j false := by
  induction rs with
  | nil => intro vs j _; rfl
  | cons r rs ih =>
    intro vs j hj
    simp only [List.foldl_cons]
    rw [ih _ j (by simp [rvStep]; omega)]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem rv_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) :
    ∀ vs : List Bool, (rs.foldl (rvStep U) vs).length = vs.length + rs.length := by
  induction rs with
  | nil => intro vs; simp
  | cons r rs ih => intro vs; simp only [List.foldl_cons, ih]; simp [rvStep]; omega

theorem rvals_len {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) : (rvals U rs).length = rs.length := by
  simp [rvals, rv_len]

theorem rvals_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) :
    rvals U (rs ++ [r]) = rvStep U (rvals U rs) r := by
  simp [rvals, List.foldl_append]

theorem sv_congr {n : ℕ} (U : Finset (Fin n)) (vs vs' : List Bool) (V : Finset (Fin n)) (G : Finset ℕ)
    (h : ∀ j ∈ G, vs.getD j false = vs'.getD j false) : sv U vs V G = sv U vs' V G := by
  unfold sv
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj) ▸ hv⟩
  · rintro ⟨j, hj, hv⟩; exact ⟨j, hj, (h j hj).symm ▸ hv⟩

def RefsLt {n : ℕ} (m : ℕ) (f : Form n) : Prop := ∀ p, f = some p → ∀ j ∈ p.2, j < m

def GoodRecs {n : ℕ} (rs : List (Rec n)) : Prop :=
  ∀ k (hk : k < rs.length), (∀ j ∈ rs[k].2.1, j < k) ∧ (∀ j ∈ rs[k].2.2.2, j < k)

theorem fv_snoc {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (r : Rec n) (f : Form n)
    (hf : RefsLt rs.length f) : fv U (rvals U (rs ++ [r])) f = fv U (rvals U rs) f := by
  rcases f with _ | p
  · rfl
  · simp only [fv]
    apply sv_congr
    intro j hj
    have hjl := hf p rfl j hj
    rw [rvals_snoc]
    simp [rvStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [rvals_len U]; exact hjl)]

theorem refs_orF {n : ℕ} (m : ℕ) (fs : List (Form n)) (h : ∀ f ∈ fs, RefsLt m f) : RefsLt m (orF fs) := by
  induction fs with
  | nil => intro p hp j hj; simp [orF] at hp; subst hp; simp at hj
  | cons f fs ih =>
    have ih' := ih (fun f' hf' => h f' (by simp [hf']))
    have hf := h f (by simp)
    intro p hp j hj
    rcases f with _ | ⟨a, b⟩
    · simp [orF] at hp
    · rcases hq : orF fs with _ | ⟨c, d⟩
      · simp [orF, hq] at hp
      · simp only [orF, hq, Option.some.injEq] at hp
        subst hp
        rcases Finset.mem_union.1 hj with hj | hj
        · exact hf _ rfl j hj
        · exact ih' _ hq j hj

theorem refs_getF {n : ℕ} (m : ℕ) (s : St n) (h : ∀ f ∈ s.fs, RefsLt m f) (i : ℕ) : RefsLt m (getF s i) := by
  unfold getF
  by_cases hi : i < s.fs.length
  · rw [List.getD_eq_getElem _ _ hi]; exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    intro p hp j hj
    simp [zeroF] at hp; subst hp; simp at hj

def Fw (W : List Bool) (g : Gate) : List Bool := W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)]

def Inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) : Prop :=
  s.fs.length = W.length ∧ (∀ f ∈ s.fs, RefsLt s.rs.length f) ∧ GoodRecs s.rs ∧
    ∀ i, W.getD i false = fv U (rvals U s.rs) (getF s i)

theorem getF_push {n : ℕ} (fs : List (Form n)) (rs : List (Rec n)) (f : Form n) (i : ℕ) :
    getF ⟨fs ++ [f], rs⟩ i = if i < fs.length then fs.getD i zeroF else if i = fs.length then f else zeroF := by
  unfold getF
  split_ifs with h1 h2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  · subst h2; simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by simp; omega)]

theorem fv_zero {n : ℕ} (U : Finset (Fin n)) (vs : List Bool) : fv U vs zeroF = false := by
  simp [fv, zeroF, sv]

theorem inv_push {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (f : Form n) (x : Bool)
    (hI : Inv U W s) (hf : RefsLt s.rs.length f) (hx : x = fv U (rvals U s.rs) f) :
    Inv U (W ++ [x]) ⟨s.fs ++ [f], s.rs⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, hg, ?_⟩
  · intro f' hf'
    rcases List.mem_append.1 hf' with h | h
    · exact hr f' h
    · simp at h; subst h; exact hf
  · intro i
    rw [getF_push]
    split_ifs with h1 h2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      exact this
    · subst h2; rw [hl]; simp [List.getD_eq_getElem?_getD, hx]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

theorem inv_rec {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (r : Rec n) (x : Bool)
    (hI : Inv U W s) (h1 : ∀ j ∈ r.2.1, j < s.rs.length) (h2 : ∀ j ∈ r.2.2.2, j < s.rs.length)
    (hx : x = (sv U (rvals U s.rs) r.1 r.2.1 && sv U (rvals U s.rs) r.2.2.1 r.2.2.2)) :
    Inv U (W ++ [x]) ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [r]⟩ := by
  obtain ⟨hl, hr, hg, hv⟩ := hI
  refine ⟨by simp [hl], ?_, ?_, ?_⟩
  · intro f' hf'
    simp only [List.length_append, List.length_cons, List.length_nil]
    rcases List.mem_append.1 hf' with h | h
    · intro p hp j hj; have := hr f' h p hp j hj; omega
    · simp at h; subst h; intro p hp j hj; simp at hp; subst hp; simp at hj; omega
  · intro k hk
    simp only [List.length_append, List.length_cons, List.length_nil] at hk
    by_cases hk' : k < s.rs.length
    · rw [List.getElem_append_left hk']; exact hg k hk'
    · have : k = s.rs.length := by omega
      subst this
      simp only [List.getElem_append_right (le_refl _), Nat.sub_self, List.getElem_cons_zero]
      exact ⟨h1, h2⟩
  · intro i
    rw [getF_push]
    split_ifs with hi1 hi2
    · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      have := hv i
      unfold getF at this
      rw [this, fv_snoc U s.rs r]
      have := hr _ (List.getElem_mem (by omega : i < s.fs.length))
      rw [List.getD_eq_getElem _ _ (by omega)]
      exact this
    · subst hi2
      rw [hl]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
        List.getElem?_cons_zero, Option.getD_some]
      have hlen : (rvals U s.rs).length = s.rs.length := rvals_len U s.rs
      simp only [fv, sv, rvals_snoc, rvStep, Finset.mem_singleton, exists_eq_left]
      rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
      simp [hx, sv]
    · rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]

def Ok (g : Gate) : Prop := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

theorem step_inv {n : ℕ} (U : Finset (Fin n)) (W : List Bool) (s : St n) (g : Gate)
    (hI : Inv U W s) (hg : Ok g) : Inv U (Fw W g) (step s g) := by
  have hv := hI.2.2.2
  have hR : ∀ i, RefsLt s.rs.length (getF s i) := refs_getF s.rs.length s hI.2.1
  obtain ⟨hop, hlen⟩ := hg
  rcases g with ⟨op, ins⟩
  simp only at hop hlen
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
      simp [GateOp.eval, fv]
    · apply inv_push U W s (getF s a) _ hI (hR a)
      have := hv a
      simp only [List.getD_eq_getElem?_getD] at this
      simp [Fw, GateOp.eval, this]
    · show Inv U (Fw W ⟨GateOp.and, [a, b]⟩) (andStep s (getF s a) (getF s b))
      have ea := hv a
      have eb := hv b
      rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩
      · apply inv_push U W s none _ hI (by intro p hp; simp at hp)
        rw [hfa] at ea; rw [hfb] at eb
        simp [Fw, GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (vb, gb)) _ hI (hfb ▸ hR b)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · apply inv_push U W s (some (va, ga)) _ hI (hfa ▸ hR a)
        rw [hfa] at ea; rw [hfb] at eb
        simp [GateOp.eval, fv] at ea eb ⊢; simp [ea, eb]
      · have ha := hR a; rw [hfa] at ha
        have hb := hR b; rw [hfb] at hb
        apply inv_rec U W s (va, ga, vb, gb) _ hI (ha _ rfl) (hb _ rfl)
        rw [hfa] at ea; rw [hfb] at eb
        simp only [fv, List.getD_eq_getElem?_getD] at ea eb
        simp [Fw, GateOp.eval, ea, eb]
    · simp at hlen
  · apply inv_push U W s (orF (ins.map (getF s))) _ hI
      (refs_orF _ _ (fun f hf => by
        obtain ⟨i, _, rfl⟩ := List.mem_map.1 hf
        exact hR i))
    rw [fv_orF]
    simp only [GateOp.eval, List.any_map]
    congr 1
    funext i
    have := hv i
    simp only [List.getD_eq_getElem?_getD] at this
    simp [Function.comp, this]

theorem fold_inv {n : ℕ} (U : Finset (Fin n)) (gs : List Gate) (hgs : ∀ g ∈ gs, Ok g) :
    ∀ (W : List Bool) (s : St n), Inv U W s → Inv U (gs.foldl Fw W) (gs.foldl step s) := by
  induction gs with
  | nil => intro W s h; exact h
  | cons g gs ih =>
    intro W s h
    simp only [List.foldl_cons]
    exact ih (fun g' hg' => hgs g' (by simp [hg'])) _ _ (step_inv U W s g h (hgs g (by simp)))

def isAnd (g : Gate) : Bool := match g.op with
  | GateOp.and => true
  | _ => false

theorem isAnd_iff (g : Gate) : isAnd g = true ↔ g.op = GateOp.and := by
  unfold isAnd
  split <;> simp_all

theorem step_rs {n : ℕ} (s : St n) (g : Gate) :
    (step s g).rs.length ≤ s.rs.length + (if isAnd g = true then 1 else 0) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step, isAnd] <;> try simp
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> simp only [step]
  · simp
  · simp
  · unfold andStep
    split <;> simp

theorem fold_rs {n : ℕ} (gs : List Gate) :
    ∀ s : St n, (gs.foldl step s).rs.length ≤ s.rs.length + gs.countP isAnd := by
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    simp only [List.foldl_cons, List.countP_cons]
    have h1 := ih (step s g)
    have h2 := step_rs s g
    split_ifs at h2 ⊢ <;> omega

theorem rvals_split {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k : ℕ) :
    rvals U rs = (rs.drop k).foldl (rvStep U) (rvals U (rs.take k)) := by
  unfold rvals
  rw [← List.foldl_append, List.take_append_drop]

theorem rvals_take {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (k j : ℕ) (hj : j < k) (hk : k ≤ rs.length) :
    (rvals U rs).getD j false = (rvals U (rs.take k)).getD j false := by
  rw [rvals_split U rs k, rv_pre]
  rw [rvals_len, List.length_take]; omega

theorem rec_val {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (k : ℕ) (hk : k < rs.length) :
    (rvals U rs).getD k false = (sv U (rvals U rs) rs[k].1 rs[k].2.1 && sv U (rvals U rs) rs[k].2.2.1 rs[k].2.2.2) := by
  rw [rvals_take U rs (k + 1) k (by omega) (by omega)]
  rw [List.take_succ_eq_append_getElem hk, rvals_snoc]
  have hl : (rvals U (rs.take k)).length = k := by rw [rvals_len, List.length_take]; omega
  simp only [rvStep]
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  simp only [List.getD_cons_zero]
  obtain ⟨h1, h2⟩ := hg k hk
  congr 1
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h1 j hj) (by omega)).symm
  · apply sv_congr; intro j hj; exact (rvals_take U rs k j (h2 j hj) (by omega)).symm

def toACC {n : ℕ} (rs : List (Rec n)) (V : Finset (Fin n)) (G : Finset ℕ) : PEqualNP.AndCount.AndCountCircuit n where
  size := rs.length
  leftVars i := rs[i].1
  leftGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.1)
  rightVars i := rs[i].2.2.1
  rightGates i := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ rs[i].2.2.2)
  outVars := V
  outGates := Finset.univ.filter (fun j : Fin rs.length => j.val ∈ G)

theorem side_eq {n : ℕ} (U : Finset (Fin n)) (m : ℕ) (B : Finset (Fin n)) (G : Finset ℕ) (i : Fin m)
    (val : Fin m → Bool) (vs : List Bool) (hG : ∀ j ∈ G, j < i.val)
    (hval : ∀ j : Fin m, j < i → val j = vs.getD j false) :
    PEqualNP.AndCount.AndCountCircuit.sideTrue U B (Finset.univ.filter (fun j : Fin m => j.val ∈ G)) i val
      = sv U vs B G := by
  unfold PEqualNP.AndCount.AndCountCircuit.sideTrue sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hji, hv⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact ⟨j.val, hj, by rw [← hval j hji]; exact hv⟩
  · rintro ⟨j, hj, hv⟩
    have hji := hG j hj
    refine ⟨⟨j, by omega⟩, by simp [hj], hji, ?_⟩
    rw [hval ⟨j, by omega⟩ hji]
    exact hv

theorem fuel {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    ∀ d (i : Fin rs.length), i.val < d →
      (toACC rs V G).gateValFuel U d i = (rvals U rs).getD i false := by
  intro d
  induction d with
  | zero => intro i hi; omega
  | succ d ih =>
    intro i hi
    rw [rec_val U rs hg i i.isLt]
    obtain ⟨h1, h2⟩ := hg i i.isLt
    simp only [PEqualNP.AndCount.AndCountCircuit.gateValFuel]
    have hv : ∀ j : Fin rs.length, j < i → (toACC rs V G).gateValFuel U d j = (rvals U rs).getD j false :=
      fun j hj => ih j (by omega)
    congr 1
    · exact side_eq U rs.length _ _ i _ _ h1 hv
    · exact side_eq U rs.length _ _ i _ _ h2 hv

theorem eval_eq {n : ℕ} (U : Finset (Fin n)) (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ)
    (hG : ∀ j ∈ G, j < rs.length) : (toACC rs V G).eval U = sv U (rvals U rs) V G := by
  unfold PEqualNP.AndCount.AndCountCircuit.eval sv
  rw [Bool.decide_or]
  congr 2
  apply propext
  constructor
  · rintro ⟨j, hj, hv⟩
    have hj' : j.val ∈ G := (Finset.mem_filter.1 hj).2
    refine ⟨j.val, hj', ?_⟩
    exact (fuel U rs hg V G rs.length j j.isLt).symm.trans hv
  · rintro ⟨j, hj, hv⟩
    refine ⟨⟨j, hG j hj⟩, Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩, ?_⟩
    exact (fuel U rs hg V G rs.length ⟨j, hG j hj⟩ (hG j hj)).trans hv

theorem wf {n : ℕ} (rs : List (Rec n)) (hg : GoodRecs rs) (V : Finset (Fin n)) (G : Finset ℕ) :
    (toACC rs V G).WellFormed := by
  intro i
  obtain ⟨h1, h2⟩ := hg i i.isLt
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · exact h1 j (Finset.mem_filter.1 hj).2
  · exact h2 j (Finset.mem_filter.1 hj).2

theorem tight_step {n : ℕ} (s : St n) (pre post : List Gate) (g : Gate)
    (ht : ((pre ++ g :: post).foldl step s).rs.length =
      s.rs.length + (pre ++ g :: post).countP isAnd)
    (hg : g.op = GateOp.and) :
    (step (pre.foldl step s) g).rs.length = (pre.foldl step s).rs.length + 1 := by
  have hp := fold_rs pre s
  have hs := step_rs (pre.foldl step s) g
  have hq := fold_rs post (step (pre.foldl step s) g)
  have ha : isAnd g = true := (isAnd_iff g).2 hg
  simp only [List.foldl_append, List.foldl_cons, List.countP_append,
    List.countP_cons, ha, ite_true] at ht
  rw [if_pos ha] at hs
  omega

theorem step_form_prefix {n : ℕ} (s : St n) (g : Gate) :
    ∃ f, (step s g).fs = s.fs ++ [f] := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step]
  all_goals first | exact ⟨_, rfl⟩ | skip
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩ <;> simp [step, andStep, hfa, hfb]

theorem step_record_prefix {n : ℕ} (s : St n) (g : Gate) :
    ∃ t, (step s g).rs = s.rs ++ t := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp only [step]
  all_goals first | exact ⟨[], by simpa only [List.append_nil]⟩ | skip
  rcases ins with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · exact ⟨[], by simp⟩
  · exact ⟨[], by simp⟩
  · rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩ <;> simp [step, andStep, hfa, hfb]

theorem fold_form_prefix {n : ℕ} (gs : List Gate) (s : St n) :
    ∃ t, (gs.foldl step s).fs = s.fs ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨f, hf⟩ := step_form_prefix s g
    obtain ⟨t, ht⟩ := ih (step s g)
    exact ⟨[f] ++ t, by simpa [List.foldl_cons, hf, List.append_assoc] using ht⟩

theorem fold_record_prefix {n : ℕ} (gs : List Gate) (s : St n) :
    ∃ t, (gs.foldl step s).rs = s.rs ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨a, ha⟩ := step_record_prefix s g
    obtain ⟨t, ht⟩ := ih (step s g)
    exact ⟨a ++ t, by simpa [List.foldl_cons, ha, List.append_assoc] using ht⟩

theorem fold_form_length {n : ℕ} (gs : List Gate) (s : St n) :
    (gs.foldl step s).fs.length = s.fs.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    obtain ⟨f, hf⟩ := step_form_prefix s g
    simp only [List.foldl_cons, ih, hf, List.length_append, List.length_cons,
      List.length_nil]
    omega

theorem retained_shape {n : ℕ} (s : St n) (g : Gate)
    (hg : g.op = GateOp.and) (hl : g.inputs.length ≤ 2)
    (hr : (step s g).rs.length = s.rs.length + 1) :
    ∃ r : Rec n, step s g =
      ⟨s.fs ++ [some (∅, {s.rs.length})], s.rs ++ [r]⟩ := by
  rcases g with ⟨op, ins⟩
  simp only at hg hl
  subst op
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [step] at hr
  · simp [step] at hr
  · rcases hfa : getF s a with _ | ⟨va, ga⟩ <;> rcases hfb : getF s b with _ | ⟨vb, gb⟩
    all_goals simp [step, andStep, hfa, hfb] at hr ⊢
  · simp at hl

theorem retained_wire {n : ℕ} (s : St n) (g : Gate) (post : List Gate)
    (hg : g.op = GateOp.and) (hl : g.inputs.length ≤ 2)
    (hr : (step s g).rs.length = s.rs.length + 1)
    (U : Finset (Fin n)) (W : List Bool)
    (hI : Inv U W (post.foldl step (step s g)))
    (V : Finset (Fin n)) (G : Finset ℕ) :
    ∃ k : Fin (post.foldl step (step s g)).rs.length,
      W.getD s.fs.length false =
        (toACC (post.foldl step (step s g)).rs V G).gateVal U k := by
  obtain ⟨r, he⟩ := retained_shape s g hg hl hr
  obtain ⟨ft, hf⟩ := fold_form_prefix post (step s g)
  obtain ⟨rt, hrt⟩ := fold_record_prefix post (step s g)
  have hk : s.rs.length < (post.foldl step (step s g)).rs.length := by
    rw [hrt, he]
    simp
  refine ⟨⟨s.rs.length, hk⟩, ?_⟩
  rw [hI.2.2.2]
  have hget : getF (post.foldl step (step s g)) s.fs.length =
      some (∅, {s.rs.length}) := by
    unfold getF
    rw [hf, he]
    simp only [List.append_assoc]
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  rw [hget]
  simpa [fv, sv, PEqualNP.AndCount.AndCountCircuit.gateVal, toACC] using
    (fuel U _ hI.2.2.1 V G _ ⟨s.rs.length, hk⟩ hk).symm


theorem convert_tight {n : ℕ} (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hfalse : ∃ U : Finset (Fin n),
      PEqualNP.MetaComplexity.circuitFun n C (fun i => decide (i ∈ U)) = false) :
    ∃ D : PEqualNP.AndCount.AndCountCircuit n,
      D.size ≤ C.gates.countP isAnd ∧
      (∀ U : Finset (Fin n), D.eval U =
        PEqualNP.MetaComplexity.circuitFun n C (fun i => decide (i ∈ U))) ∧
      (D.size = C.gates.countP isAnd →
        ∀ (pre post : List Gate) (g : Gate), C.gates = pre ++ g :: post →
          g.op = GateOp.and → ∀ U : Finset (Fin n),
          ∃ k : Fin D.size,
            (C.gates.foldl Fw (List.ofFn fun i : Fin n => decide (i ∈ U))).getD
              (n + pre.length) false = D.gateVal U k) := by
  obtain ⟨U0, hU0⟩ := hfalse
  have hok : ∀ g ∈ C.gates, Ok g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hmono g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  let s0 : St n := ⟨List.ofFn (fun i : Fin n => some ({i}, ∅)), []⟩
  let s := C.gates.foldl step s0
  have hinit : ∀ U : Finset (Fin n),
      Inv U (List.ofFn fun x : Fin n => decide (x ∈ U)) s0 := by
    intro U
    refine ⟨by simp [s0], ?_, ?_, ?_⟩
    · intro f hf p hp j hj
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hf
      simp only [Option.some.injEq] at hp
      subst hp
      simp at hj
    · intro k hk; simp [s0] at hk
    · intro i
      by_cases hi : i < n
      · simp only [getF, s0]
        rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn,
          List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn]
        simp [fv, sv]
      · rw [List.getD_eq_default _ _ (by simp; omega)]
        simp only [getF, s0]
        rw [List.getD_eq_default _ _ (by simp; omega), fv_zero]
  have hinv : ∀ U : Finset (Fin n),
      Inv U (C.gates.foldl Fw (List.ofFn fun x : Fin n => decide (x ∈ U))) s :=
    fun U => fold_inv U C.gates hok _ _ (hinit U)
  have hfun : ∀ U : Finset (Fin n),
      PEqualNP.MetaComplexity.circuitFun n C (fun x => decide (x ∈ U)) =
        fv U (rvals U s.rs) (getF s C.output) := fun U => (hinv U).2.2.2 C.output
  rcases hfo : getF s C.output with _ | ⟨V, G⟩
  · have := hfun U0
    rw [hfo, hU0] at this
    simp [fv] at this
  · have hG : ∀ j ∈ G, j < s.rs.length :=
      refs_getF _ s (hinv U0).2.1 C.output _ hfo
    have hgood := (hinv U0).2.2.1
    refine ⟨toACC s.rs V G, ?_, ?_, ?_⟩
    · have h := fold_rs C.gates s0
      simpa only [toACC, s0, List.length_nil, Nat.zero_add] using h
    · intro U
      rw [eval_eq U s.rs hgood V G hG, hfun U, hfo]
      rfl
    · intro ht pre post g hc hg U
      have hmem : g ∈ C.gates := by rw [hc]; simp
      have hlen := (hok g hmem).2
      have ht' : ((pre ++ g :: post).foldl step s0).rs.length =
          s0.rs.length + (pre ++ g :: post).countP isAnd := by
        simpa only [toACC, s, hc, s0, List.length_nil, Nat.zero_add] using ht
      have hretain := tight_step s0 pre post g ht' hg
      have hI : Inv U
          (C.gates.foldl Fw (List.ofFn fun i : Fin n => decide (i ∈ U)))
          (post.foldl step (step (pre.foldl step s0) g)) := by
        simpa only [s, hc, List.foldl_append, List.foldl_cons] using hinv U
      have hw := retained_wire (pre.foldl step s0) g post hg hlen hretain U _ hI V G
      have hstate : post.foldl step (step (pre.foldl step s0) g) = s := by
        simp only [s, hc, List.foldl_append, List.foldl_cons]
      rw [hstate] at hw
      obtain ⟨k, hk⟩ := hw
      refine ⟨k, ?_⟩
      have hfl : (pre.foldl step s0).fs.length = n + pre.length := by
        simpa only [s0, List.length_ofFn] using fold_form_length pre s0
      simpa only [hfl] using hk

end PEqualNP.Outside.L_meta_650_aux.TightConversion

namespace PEqualNP.Outside.L_meta_650_aux.FiveOwnerOrdinaryClean

open PEqualNP.CircuitLowerBounds

 theorem andcount_at_least_five (D : PEqualNP.AndCount.AndCountCircuit 16)
    (hcorrect : ∀ U : Finset (Fin 16), D.eval U = true ↔ FiveOwnerNegatives.hasEdge U) :
    5 ≤ D.size := by
  have hneg : ∀ U ∈ FiveOwnerNegatives.family, D.eval U = false := by
    intro U hU
    cases hv : D.eval U
    · rfl
    · exact False.elim (FiveOwnerNegatives.family_negative U hU ((hcorrect U).mp hv))
  have hpos : ∀ U ∈ FiveOwnerNegatives.family, ∀ V ∈ FiveOwnerNegatives.family,
      U ≠ V → D.eval (U ∪ V) = true := by
    intro U hU V hV hne
    exact (hcorrect _).mpr (FiveOwnerNegatives.pair_positive U V hU hV hne)
  have hp := FiveOwnerBudget.packing D FiveOwnerNegatives.family hneg hpos
  have hlo : 30 ≤ ∑ U ∈ FiveOwnerNegatives.family,
      2 ^ (FiveOwnerBudget.free D U).card := by
    calc
      30 = ∑ _U ∈ FiveOwnerNegatives.family, (1 : ℕ) := by
        simp [FiveOwnerNegatives.family_card]
      _ ≤ _ := Finset.sum_le_sum fun U _ => Nat.one_le_pow _ _ (by decide)
  by_contra h
  have hs : D.size ≤ 4 := by omega
  have hh : 2 ^ D.size ≤ 16 := by
    calc
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) hs
      _ = 16 := rfl
  omega

 theorem ordinary_and_clean (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hsize : C.gates.countP TightConversion.isAnd ≤ 5)
    (hcorrect : ∀ U : Finset (Fin 16),
      PEqualNP.MetaComplexity.circuitFun 16 C (fun i => decide (i ∈ U)) = true ↔
        FiveOwnerNegatives.hasEdge U) :
    ∀ (pre post : List Gate) (g : Gate), C.gates = pre ++ g :: post →
      g.op = GateOp.and → ∀ U : Finset (Fin 16), ¬FiveOwnerNegatives.hasEdge U →
      (C.wires (List.ofFn fun i : Fin 16 => decide (i ∈ U))).getD
        (16 + pre.length) false = false := by
  have hfalse : ∃ U : Finset (Fin 16),
      PEqualNP.MetaComplexity.circuitFun 16 C (fun i => decide (i ∈ U)) = false := by
    refine ⟨∅, ?_⟩
    cases hv : PEqualNP.MetaComplexity.circuitFun 16 C (fun i => decide (i ∈ (∅ : Finset (Fin 16))))
    · rfl
    · have := (hcorrect ∅).mp hv
      simp [FiveOwnerNegatives.hasEdge] at this
  obtain ⟨D, hdsize, heval, hwire⟩ := TightConversion.convert_tight C hm hfalse
  have hdcorrect : ∀ U : Finset (Fin 16),
      D.eval U = true ↔ FiveOwnerNegatives.hasEdge U := by
    intro U
    rw [heval U]
    exact hcorrect U
  have hmin := andcount_at_least_five D hdcorrect
  have ht : D.size = C.gates.countP TightConversion.isAnd := by omega
  have hclean := FiveOwnerClean.five_and_clean D (by omega) hdcorrect
  intro pre post g hc hg U hU
  obtain ⟨k, hk⟩ := hwire ht pre post g hc hg U
  change (C.gates.foldl TightConversion.Fw
    (List.ofFn fun i : Fin 16 => decide (i ∈ U))).getD (16 + pre.length) false = false
  exact hk.trans (hclean k U hU)

end PEqualNP.Outside.L_meta_650_aux.FiveOwnerOrdinaryClean
