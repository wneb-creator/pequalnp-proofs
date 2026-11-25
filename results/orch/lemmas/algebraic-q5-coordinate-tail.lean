theorem equality_three_coordinate_normalize : ∀ M : Finset (Fin 3),
    M.card = 1 ∨ M.card = 2 → ∃ σ : Equiv.Perm (Fin 3),
      M.image σ = {0} ∨ M.image σ = {0,1} := by
  decide +kernel

theorem equality_residual_coordinates {D : Dag} {b : Fin 14 → ℕ}
    (hres : (residualUnits 14 D b).card = 3)
    (h7 : (ru D b 7).card = 1 ∨ (ru D b 7).card = 2) :
    ∃ a : Fin 3 → (Σ _ : ℕ, ℕ), Function.Injective a ∧
      (∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) ∧
      ((Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1)) = {0} ∨
        (Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1)) = {0,1}) := by
  classical
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hres)
  let a0 : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have inj0 : Function.Injective a0 :=
    fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto0 : ∀ u, u ∈ S ↔ ∃ k, a0 k = u := by
    intro u
    constructor
    · intro hu
      exact ⟨e ⟨u,hu⟩,by simp [a0]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  let M := Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a0 k).1)
  have image : M.image a0 = ru D b 7 := by
    ext u
    constructor
    · rintro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
      exact mem_ru.2 ⟨(onto0 _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
    · intro hu
      obtain ⟨hur,hu7⟩ := mem_ru.1 hu
      obtain ⟨k,rfl⟩ := (onto0 u).1 hur
      exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hu7⟩,rfl⟩
  have card : M.card = (ru D b 7).card := by
    rw [← image,Finset.card_image_of_injective _ inj0]
  obtain ⟨σ,hσ⟩ := equality_three_coordinate_normalize M (by omega)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => a0 (σ.symm k)
  refine ⟨a,inj0.comp σ.symm.injective,?_,?_⟩
  · intro u
    rw [onto0]
    constructor
    · rintro ⟨k,rfl⟩
      exact ⟨σ k,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact ⟨σ.symm k,rfl⟩
  · have same : Finset.univ.filter (fun k => (7 : Fin 14) ∈ supp 14 D (a k).1) = M.image σ := by
      ext k
      simp only [M,a,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
      constructor
      · intro hk
        exact ⟨σ.symm k,hk,σ.apply_symm_apply k⟩
      · rintro ⟨j,hj,rfl⟩
        simpa using hj
    rw [same]
    exact hσ

noncomputable def equality_coordinate_set {D : Dag}
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (x : Fin 14) : Finset (Fin 3) := by
  classical
  exact Finset.univ.filter (fun k => x ∈ supp 14 D (a k).1)

theorem equality_coordinate_image {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x : Fin 14) :
    (equality_coordinate_set (D := D) a x).image a = ru D b x := by
  classical
  ext u
  constructor
  · intro hu
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
    exact mem_ru.2 ⟨(onto _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
  · intro hu
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    obtain ⟨k,rfl⟩ := (onto u).1 hur
    exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩,rfl⟩

theorem equality_coordinate_card {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x : Fin 14) :
    (equality_coordinate_set (D := D) a x).card = (ru D b x).card := by
  rw [← equality_coordinate_image a onto x,Finset.card_image_of_injective _ injective]

theorem equality_coordinate_subset {D : Dag} {b : Fin 14 → ℕ}
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (x y : Fin 14) :
    equality_coordinate_set (D := D) a x ⊆ equality_coordinate_set (D := D) a y ↔
      ∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → y ∈ supp 14 D u.1 := by
  classical
  constructor
  · intro sub u hu hx
    obtain ⟨k,rfl⟩ := (onto u).1 hu
    exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hx⟩))).2
  · intro inc k hk
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,inc (a k) ((onto _).2 ⟨k,rfl⟩)
      (Finset.mem_filter.1 hk).2⟩
