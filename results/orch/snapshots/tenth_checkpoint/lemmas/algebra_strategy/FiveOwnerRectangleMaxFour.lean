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


end PEqualNP.Outside.L_meta_650_aux.FiveOwnerRectangles
