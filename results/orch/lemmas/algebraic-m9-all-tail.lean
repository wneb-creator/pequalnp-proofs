theorem equality_m9_all_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) :
    ∃ α β : Fin 3,
      m9_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β ∧
      ∀ z ∈ ({3,4,6} : Finset (Fin 14)), (equality_coordinate_set (D := D) a z).Nonempty →
        m9_point_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t))
          α β (equality_coordinate_set (D := D) a z) := by
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  obtain ⟨α,β,e2,e5⟩ := equality_m9_extras pos hpos hI missing2 missing5
  refine ⟨α,β,equality_m9_constraints h hD h14 b hb pos hpos hI missing2 missing5
    hprotected a injective onto α β e2 e5,?_⟩
  intro z hz positive
  exact equality_m9_point_constraints h hD b hb pos hpos hI hprotected a injective onto
    α β e2 e5 hz positive
