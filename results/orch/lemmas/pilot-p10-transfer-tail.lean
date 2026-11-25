
def pilotP10Point (i : Fin 4) : Fin 14 := ⟨i.val, by omega⟩
def pilotP10Line (t : Fin 7) : Fin 14 := Fin.natAdd 7 t

theorem pilotP10Point_injective : Function.Injective pilotP10Point := by
  intro i j hij
  apply Fin.ext
  exact congrArg (Fin.val : Fin 14 → ℕ) hij

theorem pilotP10Geometry :
    (∀ i : Fin 4, pilotP10Point i ∈ ({0,1,2,3} : Finset (Fin 14))) ∧
    (∀ t : Fin 7, pilotP10Line t ∉ ({0,1,2,3} : Finset (Fin 14))) ∧
    (∀ i : Fin 4, ∀ t : Fin 7, t ∈ p10_nb i ↔ Adj (pilotP10Point i) (pilotP10Line t)) ∧
    (∀ t : Fin 7, t ≠ 0 → ∃ z : Fin 14,
      z ∉ ({0,1,2,3} : Finset (Fin 14)) ∧ Adj (pilotP10Line t) z) := by
  simp only [← hc_adjB_iff]
  decide +kernel

theorem pilotP10_constraints {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3}) (hB : Bplus 14 D ≤ 12) :
    ∃ r : Fin 7 → Finset (Fin 2), p10_constraints r := by
  classical
  obtain ⟨b,hb⟩ := exists_pureBranch h hD
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hp := inelig_card_add 14 D
  rw [hI,show ({0,1,2,3} : Finset (Fin 14)).card = 4 from rfl] at hp
  have lower := tri012 h hD (fun i hi => by
    rw [hI]
    exact (by decide : ({0,1,2} : Finset (Fin 14)) ⊆ {0,1,2,3}) hi)
  have hres := card_residual h.1 b hb
  have hcard : (residualUnits 14 D b).card = 2 := by omega
  let S := residualUnits 14 D b
  let e : (↑S) ≃ Fin 2 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)
  let a : Fin 2 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have ainj : Function.Injective a := fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u := by
    intro u
    constructor
    · intro hu
      exact ⟨e ⟨u,hu⟩,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  let r : Fin 7 → Finset (Fin 2) := fun t =>
    Finset.univ.filter (fun k => pilotP10Line t ∈ supp 14 D (a k).1)
  have image (t : Fin 7) : (r t).image a = ru D b (pilotP10Line t) := by
    ext u
    constructor
    · rintro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
      exact mem_ru.2 ⟨(onto _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
    · intro hu
      obtain ⟨hur,hux⟩ := mem_ru.1 hu
      obtain ⟨k,rfl⟩ := (onto u).1 hur
      exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩,rfl⟩
  have card (t : Fin 7) : (r t).card = (ru D b (pilotP10Line t)).card := by
    rw [← image t,Finset.card_image_of_injective _ ainj]
  have point_in (i : Fin 4) : pilotP10Point i ∈ ineligSet 14 D := by
    rw [hI]
    exact pilotP10Geometry.1 i
  have line_el (t : Fin 7) : pilotP10Line t ∈ eligSet 14 D := by
    by_contra hn
    exact pilotP10Geometry.2.1 t (hI ▸ sem_mem_inelig.2 hn)
  have forced (i : Fin 4) (t : Fin 7) (ht : t ∈ p10_forcedSet r i) :
      pilotP10Line t ∈ supp 14 D (src D (pos (pilotP10Point i))) := by
    rcases Finset.mem_union.1 ht with hadj | hforced
    · exact (hpos.1 _ (point_in i)).2.2.1 _ ((pilotP10Geometry.2.2.1 i t).1 hadj)
    · obtain ⟨x,hx,hn,hs⟩ := (Finset.mem_filter.1 hforced).2
      obtain ⟨k,hk⟩ := hn
      have hkx := (Finset.mem_filter.1 hk).2
      have hkt := (Finset.mem_filter.1 (hs hk)).2
      apply equality_residual_co_label h hD b hb pos hpos (line_el x) (line_el t)
        (point_in i) ((pilotP10Geometry.2.2.1 i x).1 hx)
      · intro u hu hux
        obtain ⟨j,rfl⟩ := (onto u).1 hu
        exact (Finset.mem_filter.1 (hs (Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩))).2
      · exact ⟨(a k).1,hkx,hkt⟩
  refine ⟨r,?_⟩
  intro t
  let J : Finset (Fin 14) :=
    (Finset.univ.filter (fun i : Fin 4 => t ∈ p10_forcedSet r i)).image pilotP10Point
  have hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧
      pilotP10Line t ∈ supp 14 D (src D (pos i)) := by
    intro i hi
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hi
    exact ⟨point_in k,forced k t (Finset.mem_filter.1 hk).2⟩
  have hJcard : J.card = (Finset.univ.filter (fun i : Fin 4 => t ∈ p10_forcedSet r i)).card :=
    Finset.card_image_of_injective _ pilotP10Point_injective
  by_cases ht : t = 0
  · have bound := equality_assigned_budget h hD b hb pos hpos J hJ
    rw [hJcard,← card t] at bound
    simpa [ht] using bound
  · obtain ⟨z,hz,hedge⟩ := pilotP10Geometry.2.2.2 t ht
    have hze : z ∈ eligSet 14 D := by
      by_contra hn
      exact hz (hI ▸ sem_mem_inelig.2 hn)
    have bound := equality_assigned_budget_extra h hD b hb pos hpos J hJ hze hedge
    rw [hJcard,← card t] at bound
    simpa [ht] using bound
