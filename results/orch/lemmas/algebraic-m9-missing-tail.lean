theorem equality_m9_range : Finset.univ.image equality_m9_line = mx_L := by decide +kernel

theorem equality_m9_neighbors_image : ∀ i : Fin 4,
    (m9_neighbors i).image equality_m9_line = sem_hw_nb (equality_m9_point i) := by
  decide +kernel

theorem equality_m9_mask_image {D : Dag} (a : Fin 3 → (Σ _ : ℕ, ℕ)) (k : Fin 3) :
    (m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k).image
      equality_m9_line = supp 14 D (a k).1 ∩ mx_L := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    refine Finset.mem_inter.2 ⟨(Finset.mem_filter.1 ((Finset.mem_filter.1 ht).2)).2,?_⟩
    rw [← equality_m9_range]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_inter.1 hx
    rw [← equality_m9_range] at hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.1 hp
    exact Finset.mem_image.2 ⟨t,Finset.mem_filter.2 ⟨Finset.mem_univ _,
      Finset.mem_filter.2 ⟨Finset.mem_univ _,hs⟩⟩,rfl⟩

theorem equality_m9_unit_missing {D : Dag} (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) (k : Fin 3) :
    m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k ≠
      m9_neighbors 2 ∧
    m9_unit_support (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) k ≠
      m9_neighbors 3 := by
  constructor
  · intro equal
    apply missing2
    refine ⟨(a k).1,?_⟩
    rw [← equality_m9_mask_image a k,equal,equality_m9_neighbors_image]
    rfl
  · intro equal
    apply missing5
    refine ⟨(a k).1,?_⟩
    rw [← equality_m9_mask_image a k,equal,equality_m9_neighbors_image]
    rfl

theorem equality_m9_assigned_extra {D : Dag} (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hI : ineligSet 14 D = {0,1,2,5,11})
    (i : Fin 4) (missing : ¬ sup_Occ 14 D mx_L (sem_hw_nb (equality_m9_point i))) :
    ∃ t : Fin 6, t ∉ m9_neighbors i ∧
      equality_m9_line t ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  by_contra hn
  apply missing
  refine ⟨src D (pos (equality_m9_point i)),?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨hs,hp⟩ := Finset.mem_inter.1 hx
    rw [← equality_m9_range] at hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.1 hp
    have ht : t ∈ m9_neighbors i := by
      by_contra no
      exact hn ⟨t,no,hs⟩
    rw [← equality_m9_neighbors_image i]
    exact Finset.mem_image_of_mem _ ht
  · intro hx
    refine Finset.mem_inter.2 ⟨(hpos.1 _ (equality_m9_ineligible hI i)).2.2.1 x
      (hw_mem_nb.1 hx),?_⟩
    rw [← equality_m9_neighbors_image i] at hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    rw [← equality_m9_range]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

theorem equality_m9_extras {D : Dag} (pos : Fin 14 → ℕ × Bool)
    (hpos : k4_Pos 14 HG D pos) (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5)) :
    ∃ α β : Fin 3,
      equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)) ∧
      equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)) := by
  obtain ⟨t,ht,hmem⟩ := equality_m9_assigned_extra pos hpos hI 2 missing2
  obtain ⟨s,hs,hmem'⟩ := equality_m9_assigned_extra pos hpos hI 3 missing5
  have g2 : ∀ t : Fin 6, t ∉ m9_neighbors 2 → ∃ α : Fin 3, m9_extra2 α = t := by decide +kernel
  have g5 : ∀ t : Fin 6, t ∉ m9_neighbors 3 → ∃ β : Fin 3, m9_extra5 β = t := by decide +kernel
  obtain ⟨α,rfl⟩ := g2 t ht
  obtain ⟨β,rfl⟩ := g5 s hs
  exact ⟨α,β,hmem,hmem'⟩

