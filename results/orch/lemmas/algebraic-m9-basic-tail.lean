theorem equality_m9_ineligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (i : Fin 4) : equality_m9_point i ∈ ineligSet 14 D := by
  rw [hI]
  exact (by decide +kernel : ∀ i : Fin 4, equality_m9_point i ∈ ({0,1,2,5,11} : Finset (Fin 14))) i

theorem equality_m9_eligible {D : Dag} (hI : ineligSet 14 D = {0,1,2,5,11})
    (t : Fin 6) : equality_m9_line t ∈ eligSet 14 D := by
  by_contra hn
  have hm := hI ▸ sem_mem_inelig.2 hn
  exact (by decide +kernel : ∀ t : Fin 6, equality_m9_line t ∉ ({0,1,2,5,11} : Finset (Fin 14))) t hm

theorem equality_m9_positive {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11}) (t : Fin 6) :
    0 < (ru D b (equality_m9_line t)).card := by
  have geometry : ∀ t : Fin 6, ∃ i j : Fin 4, ∃ z : Fin 14,
      i ≠ j ∧ hc_adjB (equality_m9_point i) (equality_m9_line t) = true ∧
      hc_adjB (equality_m9_point j) (equality_m9_line t) = true ∧
      hc_adjB (equality_m9_line t) z = true ∧
      z ≠ equality_m9_point i ∧ z ≠ equality_m9_point j := by decide +kernel
  obtain ⟨i,j,z,hij,hix,hjx,hxz,hzi,hzj⟩ := geometry t
  exact equality_two_assigned_positive h hD b hb pos hpos (equality_m9_ineligible hI i)
    (equality_m9_ineligible hI j) (fun equal => hij (equality_m9_point_injective equal))
    ((hc_adjB_iff _ _).1 hix) ((hc_adjB_iff _ _).1 hjx) ((hc_adjB_iff _ _).1 hxz) hzi hzj

theorem equality_m9_coordinate_proper {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (h14 : totalSurplus 14 D ≤ 14) (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u) (t : Fin 6) :
    equality_coordinate_set (D := D) a (equality_m9_line t) ≠ Finset.univ := by
  classical
  intro full
  have hall : ∀ u ∈ residualUnits 14 D b, equality_m9_line t ∈ supp 14 D u.1 := by
    intro u hu
    obtain ⟨k,rfl⟩ := (onto u).1 hu
    have member : k ∈ equality_coordinate_set (D := D) a (equality_m9_line t) := by
      rw [full]; exact Finset.mem_univ _
    exact (Finset.mem_filter.1 member).2
  let X := (Finset.univ.erase t).image equality_m9_line
  have hx : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ equality_m9_line t ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → equality_m9_line t ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ equality_m9_line t ∈ supp 14 D w := by
    intro x hx
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI s)
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    exact ⟨equality_m9_eligible hI s,
      fun eq => (Finset.mem_erase.1 hs).1 (equality_m9_line_injective eq),
      fun u hu _ => hall u hu,u.1,hux,hall u hur⟩
  have bound := cf_six h hD b hb (equality_m9_cf_good t) (equality_m9_eligible hI t) X hx
  have Xcard : X.card = 5 := by
    rw [Finset.card_image_of_injective _ equality_m9_line_injective]
    simp
  have card := equality_coordinate_card a injective onto (equality_m9_line t)
  rw [full,Finset.card_univ,Fintype.card_fin] at card
  rw [Xcard] at bound
  omega

theorem equality_m9_forced_mem {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (pos : Fin 14 → ℕ × Bool) (hpos : k4_Pos 14 HG D pos)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (a : Fin 3 → (Σ _ : ℕ, ℕ))
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (α β : Fin 3)
    (extra2 : equality_m9_line (m9_extra2 α) ∈ supp 14 D (src D (pos 2)))
    (extra5 : equality_m9_line (m9_extra5 β) ∈ supp 14 D (src D (pos 5)))
    (i : Fin 4) (t : Fin 6)
    (ht : t ∈ m9_forced (fun s => equality_coordinate_set (D := D) a (equality_m9_line s)) α β i) :
    equality_m9_line t ∈ supp 14 D (src D (pos (equality_m9_point i))) := by
  classical
  rcases (Finset.mem_filter.1 ht).2 with ⟨x,hx,subset⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have inclusion := (equality_coordinate_subset a onto (equality_m9_line x)
      (equality_m9_line t)).1 subset
    obtain ⟨u,hu⟩ := Finset.card_pos.1 (equality_m9_positive h hD b hb pos hpos hI x)
    obtain ⟨hur,hux⟩ := mem_ru.1 hu
    exact equality_residual_co_label h hD b hb pos hpos (equality_m9_eligible hI x)
      (equality_m9_eligible hI t) (equality_m9_ineligible hI i)
      ((hc_adjB_iff _ _).1 ((equality_m9_adjacency i x).1 hx)) inclusion
      ⟨u.1,hux,inclusion u hur hux⟩
  · exact extra2
  · exact extra5

