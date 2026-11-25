theorem equality_m9_point_eligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14))) : z ∈ eligSet 14 D := by
  by_contra hn
  exact Finset.disjoint_left.1
    (by decide : Disjoint ({3,4,6} : Finset (Fin 14)) {0,1,2,5,11}) hz
    (hI ▸ sem_mem_inelig.2 hn)

theorem equality_m9_point_forced_mem {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14))) (i : Fin 4)
    (hi : i ∈ m9_point_forced (fun s => equality_coordinate_set (D := D) a (equality_m9_line s))
      (equality_coordinate_set (D := D) a z)) :
    z ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  obtain ⟨x,hx,subset⟩ := (Finset.mem_filter.1 hi).2
  have inclusion := (equality_coordinate_subset a onto (equality_m9_line x) z).1 subset
  obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI x)
  obtain ⟨hur,hux⟩ := mem_ru.1 hu
  exact equality_residual_co_label h hD b hb pos hpos (equality_m9_eligible hI x)
    (equality_m9_point_eligible hI hz) (equality_m9_ineligible hI i)
    ((hc_adjB_iff _ _).1 ((equality_m9_adjacency i x).1 hx)) inclusion
    ⟨u.1,hux,inclusion u hur hux⟩

theorem equality_m9_point_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    {z : Fin 14} (hz : z ∈ ({3,4,6} : Finset (Fin 14)))
    (positive : (equality_coordinate_set (D := D) a z).Nonempty) :
    m9_point_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t))
      α β (equality_coordinate_set (D := D) a z) := by
  classical
  let r := fun t => equality_coordinate_set (D := D) a (equality_m9_line t)
  let T := equality_coordinate_set (D := D) a z
  have hi11 : (11 : Fin 14) ∈ ineligSet 14 D := by rw [hI]; decide
  have edge11 : Adj 11 z := (hc_adjB_iff _ _).1
    ((by decide +kernel : ∀ z ∈ ({3,4,6} : Finset (Fin 14)), hc_adjB 11 z = true) z hz)
  have no11 : ∀ J : Finset (Fin 4), (11 : Fin 14) ∉ J.image equality_m9_point := by
    intro J member
    obtain ⟨i,_,eq⟩ := Finset.mem_image.1 member
    exact (by decide +kernel : ∀ i : Fin 4, equality_m9_point i ≠ (11 : Fin 14)) i eq
  refine ⟨positive,?_,?_,?_⟩
  · intro i saturated forced
    have full := equality_m9_saturated_full h hD b hb pos hpos hI hprotected a injective onto
      α β extra2 extra5 i saturated
    have mem := equality_m9_point_forced_mem h hD b hb pos hpos hI a onto hz (m9_protected i) forced
    have edge := (full z).1 mem
    have no := (by decide +kernel : ∀ i : Fin 2, ∀ z ∈ ({3,4,6} : Finset (Fin 14)),
      hc_adjB (equality_m9_point (m9_protected i)) z = false) i z hz
    have yes := (hc_adjB_iff _ _).2 edge
    rw [no] at yes
    exact Bool.false_ne_true yes
  · let J := (m9_point_forced r T).image equality_m9_point
    have hJ : ∀ i ∈ insert 11 J, i ∈ ineligSet 14 D ∧ z ∈ supp 14 D (src D (pos i)) := by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact ⟨hi11,(hpos.1 11 hi11).2.2.1 z edge11⟩
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
        exact ⟨equality_m9_ineligible hI j,
          equality_m9_point_forced_mem h hD b hb pos hpos hI a onto hz j hj⟩
    have geo : ∀ z ∈ ({3,4,6} : Finset (Fin 14)), ∃ t : Fin 6,
        hc_adjB z (equality_m9_line t) = true := by decide +kernel
    obtain ⟨t,edge⟩ := geo z hz
    have bound := equality_assigned_budget_extra h hD b hb pos hpos (insert 11 J) hJ
      (equality_m9_eligible hI t) ((hc_adjB_iff _ _).1 edge)
    have card : J.card = (m9_point_forced r T).card :=
      Finset.card_image_of_injective _ equality_m9_point_injective
    rw [Finset.card_insert_of_notMem (no11 _),card] at bound
    have tc := equality_coordinate_card a injective onto z
    change T.card = (ru D b z).card at tc
    change (m9_point_forced r T).card ≤ T.card
    omega
  · intro t
    by_cases inclusion : T ⊆ r t
    · let J := (m9_consumers r α β t).image equality_m9_point
      have inc := (equality_coordinate_subset a onto z (equality_m9_line t)).1 inclusion
      obtain ⟨k,hk⟩ := positive
      have huz : z ∈ supp 14 D (a k).1 := (Finset.mem_filter.1 hk).2
      have hur : a k ∈ residualUnits 14 D b := (onto _).2 ⟨k,rfl⟩
      have line11 := equality_residual_co_label h hD b hb pos hpos
        (equality_m9_point_eligible hI hz) (equality_m9_eligible hI t) hi11 edge11 inc
        ⟨(a k).1,huz,inc (a k) hur huz⟩
      have hJ : ∀ i ∈ insert 11 J, i ∈ ineligSet 14 D ∧
          equality_m9_line t ∈ supp 14 D (src D (pos i)) := by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨hi11,line11⟩
        · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
          exact ⟨equality_m9_ineligible hI j,
            equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 j t
              (Finset.mem_filter.1 hj).2⟩
      obtain ⟨z',hz',edge⟩ := equality_m9_extra_neighbor hI t
      have bound := equality_assigned_budget_extra h hD b hb pos hpos (insert 11 J) hJ hz' edge
      have card : J.card = (m9_consumers r α β t).card :=
        Finset.card_image_of_injective _ equality_m9_point_injective
      rw [Finset.card_insert_of_notMem (no11 _),card] at bound
      have rc := equality_coordinate_card a injective onto (equality_m9_line t)
      change (r t).card = (ru D b (equality_m9_line t)).card at rc
      change (m9_consumers r α β t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card
      rw [ite_eq_left inclusion]
      omega
    · have bound := equality_m9_consumer_budget h hD b hb pos hpos hI a injective onto
        α β extra2 extra5 t
      change (m9_consumers r α β t).card + (if T ⊆ r t then 1 else 0) ≤ 1 + (r t).card
      rw [ite_eq_right inclusion,Nat.add_zero]
      exact bound

