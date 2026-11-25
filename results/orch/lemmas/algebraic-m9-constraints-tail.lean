theorem equality_m9_extra_neighbor {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (t : Fin 6) : ∃ z : Fin 14, z ∈ eligSet 14 D ∧ Adj (equality_m9_line t) z := by
  have geo : ∀ t : Fin 6, ∃ z : Fin 14,
      z ∉ ({0,1,2,5,11} : Finset (Fin 14)) ∧ hc_adjB (equality_m9_line t) z = true := by
    decide +kernel
  obtain ⟨z,hz,edge⟩ := geo t
  refine ⟨z,?_,(hc_adjB_iff _ _).1 edge⟩
  by_contra hn
  exact hz (hI ▸ sem_mem_inelig.2 hn)

theorem equality_m9_consumer_budget {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5))) (t : Fin 6) :
    (m9_consumers (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β t).card ≤
      1 + (equality_coordinate_set (D := D) a (equality_m9_line t)).card := by
  classical
  let r := fun s => equality_coordinate_set (D := D) a (equality_m9_line s)
  let J := (m9_consumers r α β t).image equality_m9_point
  have hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧
      equality_m9_line t ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.1 hi
    exact ⟨equality_m9_ineligible hI j,
      equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 j t
        (Finset.mem_filter.1 hj).2⟩
  obtain ⟨z,hz,edge⟩ := equality_m9_extra_neighbor hI t
  have budget := equality_assigned_budget_extra h hD b hb pos hpos J hJ hz edge
  have card : J.card = (m9_consumers r α β t).card :=
    Finset.card_image_of_injective _ equality_m9_point_injective
  have rcard := equality_coordinate_card a injective onto (equality_m9_line t)
  rw [card,← rcard] at budget
  dsimp [r] at budget
  omega

theorem equality_m9_saturated_full {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
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
    (i : Fin 2)
    (saturated : m9_saturated (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β i) :
    ∀ v, v ∈ supp 14 D (src D (pos (equality_m9_point (m9_protected i)))) ↔
      Adj (equality_m9_point (m9_protected i)) v := by
  classical
  let r := fun s => equality_coordinate_set (D := D) a (equality_m9_line s)
  obtain ⟨x,hx,sat⟩ := saturated
  let J := (m9_consumers r α β x).image equality_m9_point
  have hJ : ∀ j ∈ J, j ∈ ineligSet 14 D ∧
      equality_m9_line x ∈ supp 14 D (src D (pos j)) := by
    intro j hj
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hj
    exact ⟨equality_m9_ineligible hI k,
      equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5 k x
        (Finset.mem_filter.1 hk).2⟩
  have hiJ : equality_m9_point (m9_protected i) ∈ J := by
    refine Finset.mem_image.2 ⟨m9_protected i,Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩,rfl⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,Or.inl ⟨x,hx,Finset.Subset.refl _⟩⟩
  have card : J.card = (m9_consumers r α β x).card :=
    Finset.card_image_of_injective _ equality_m9_point_injective
  have rcard := equality_coordinate_card a injective onto (equality_m9_line x)
  obtain ⟨z,hz,edge⟩ := equality_m9_extra_neighbor hI x
  apply equality_saturated_slot_full h hD b hb pos hpos J hJ hiJ
    ((hc_adjB_iff _ _).1 ((equality_m9_adjacency (m9_protected i) x).1 hx)) hz edge
  · rw [card]
    change (m9_consumers r α β x).card = 1 + (r x).card at sat
    change (r x).card = (ru D b (equality_m9_line x)).card at rcard
    omega
  · exact hprotected _ ((by decide +kernel : ∀ i : Fin 2,
      equality_m9_point (m9_protected i) ∈ ({0,1} : Finset (Fin 14))) i)

theorem equality_m9_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (hprotected : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5))) :
    m9_constraints (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β := by
  classical
  refine ⟨?_,?_,?_,?_⟩
  · intro t
    refine ⟨Finset.card_pos.1 ?_,equality_m9_coordinate_proper h hD h14 b hb pos hpos hI a injective onto t⟩
    rw [equality_coordinate_card a injective onto]
    exact equality_m9_positive h hD b hb pos hpos hI t
  · exact equality_m9_unit_missing a missing2 missing5
  · exact equality_m9_consumer_budget h hD b hb pos hpos hI a injective onto α β extra2 extra5
  · intro i saturated t ht
    have full := equality_m9_saturated_full h hD b hb pos hpos hI hprotected a injective onto
      α β extra2 extra5 i saturated
    have mem := equality_m9_forced_mem h hD b hb pos hpos hI a onto α β extra2 extra5
      (m9_protected i) t ht
    exact (equality_m9_adjacency _ _).2 ((hc_adjB_iff _ _).2 ((full _).1 mem))

