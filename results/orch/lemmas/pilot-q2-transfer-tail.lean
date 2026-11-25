def qa_line (t : Fin 7) : Fin 14 := Fin.natAdd 7 t

def qa_point (i : Fin 4) : Fin 14 := ⟨i.val,by omega⟩

noncomputable def qa_mask (D : Dag) (w : ℕ) : Finset (Fin 7) := by
  classical
  exact Finset.univ.filter (fun t => qa_line t ∈ supp 14 D w)

lemma qa_line_injective : Function.Injective qa_line := by
  intro i j hij
  apply Fin.ext
  have := congrArg (Fin.val : Fin 14 → ℕ) hij
  simp only [qa_line, Fin.val_natAdd] at this
  omega

lemma qa_point_injective : Function.Injective qa_point := by
  intro i j hij
  apply Fin.ext
  exact congrArg (Fin.val : Fin 14 → ℕ) hij

lemma qa_geometry :
    (∀ i : Fin 4, qa_point i ∈ ({0,1,2,3} : Finset (Fin 14))) ∧
    (∀ t : Fin 7, qa_line t ∉ ({0,1,2,3} : Finset (Fin 14))) ∧
    (∀ i : Fin 4, ∀ t : Fin 7, t ∈ qa_nb i ↔ Adj (qa_point i) (qa_line t)) ∧
    (∀ t : Fin 7, t ≠ 0 → ∃ z : Fin 14,
      z ∉ ({0,1,2,3} : Finset (Fin 14)) ∧ Adj (qa_line t) z) ∧
    (∀ t : Fin 7, ∃ i ∈ ({0,1,3} : Finset (Fin 4)),
      (0 : Fin 7) ∈ qa_nb i ∧ t ∈ qa_nb i) := by
  simp only [← hc_adjB_iff]
  decide +kernel

lemma qa_circuit_residual_exclusion {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (hI : ineligSet 14 D = {0,1,2,3}) (hB : Bplus 14 D = 13)
    (hS : totalSurplus 14 D ≤ 14)
    (occurs : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), ∃ w, qa_mask D w = qa_nb i)
    (shape : ∃ S : Finset (Fin 7), ∀ w, qa_allowed S (qa_mask D w)) : False := by
  classical
  obtain ⟨S,hshape⟩ := shape
  obtain ⟨b,hb⟩ := exists_pureBranch h hD
  obtain ⟨pos,hpos⟩ := k4_assigned sem_heawood_gr h (sem_heawood_comp hD)
  have hp := inelig_card_add 14 D
  rw [hI,show ({0,1,2,3} : Finset (Fin 14)).card = 4 from rfl] at hp
  have hres := card_residual h.1 b hb
  have hcard : (residualUnits 14 D b).card = 3 := by omega
  let R := residualUnits 14 D b
  let e : (↑R) ≃ Fin 3 := Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hcard)
  let a : Fin 3 → (Σ _ : ℕ, ℕ) := fun k => (e.symm k).val
  have ainj : Function.Injective a := fun i j equal => e.symm.injective (Subtype.ext equal)
  have onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u := by
    intro u
    constructor
    · intro hu
      exact ⟨e ⟨u,hu⟩,by simp [a]⟩
    · rintro ⟨k,rfl⟩
      exact (e.symm k).property
  let r : Fin 7 → Finset (Fin 3) := fun t =>
    Finset.univ.filter (fun k => qa_line t ∈ supp 14 D (a k).1)
  have image (t : Fin 7) : (r t).image a = ru D b (qa_line t) := by
    ext u
    constructor
    · rintro hu
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hu
      exact mem_ru.2 ⟨(onto _).2 ⟨k,rfl⟩,(Finset.mem_filter.1 hk).2⟩
    · intro hu
      obtain ⟨hur,hux⟩ := mem_ru.1 hu
      obtain ⟨k,rfl⟩ := (onto u).1 hur
      exact Finset.mem_image.2 ⟨k,Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩,rfl⟩
  have card (t : Fin 7) : (r t).card = (ru D b (qa_line t)).card := by
    rw [← image t,Finset.card_image_of_injective _ ainj]
  have point_in (i : Fin 4) : qa_point i ∈ ineligSet 14 D := by
    rw [hI]
    exact qa_geometry.1 i
  have line_el (t : Fin 7) : qa_line t ∈ eligSet 14 D := by
    by_contra hn
    exact qa_geometry.2.1 t (hI ▸ sem_mem_inelig.2 hn)
  let A : Fin 4 → Finset (Fin 7) := fun i => qa_mask D (src D (pos (qa_point i)))
  have supersets (i : Fin 4) : qa_nb i ⊆ A i := by
    intro t ht
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      (hpos.1 _ (point_in i)).2.2.1 _ ((qa_geometry.2.2.1 i t).1 ht)⟩
  have choices (i : Fin 4) : A i = qa_nb 0 ∨ A i = qa_nb 1 ∨ A i = qa_nb 3 ∨ A i = S := by
    rcases hshape (src D (pos (qa_point i))) with low | h0 | h1 | h3 | hS
    · have bound := Finset.card_le_card (supersets i)
      have nbcard := (by decide : ∀ i : Fin 4, (qa_nb i).card = 3) i
      change (A i).card ≤ 2 at low
      omega
    · exact Or.inl h0
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl h3))
    · exact Or.inr (Or.inr (Or.inr hS))
  have missing : A 2 = S := by
    have sub := supersets 2
    rcases choices 2 with eq | eq | eq | eq
    · rw [eq] at sub
      exact ((by decide : ¬ qa_nb 2 ⊆ qa_nb 0) sub).elim
    · rw [eq] at sub
      exact ((by decide : ¬ qa_nb 2 ⊆ qa_nb 1) sub).elim
    · rw [eq] at sub
      exact ((by decide : ¬ qa_nb 2 ⊆ qa_nb 3) sub).elim
    · exact eq
  have allowed (j : Fin 3) : qa_allowed S (qa_unit r j) := by
    have eq : qa_unit r j = qa_mask D (a j).1 := by
      ext t
      simp only [qa_unit,qa_mask,Finset.mem_filter,Finset.mem_univ,true_and,r]
    rw [eq]
    exact hshape _
  have labels (i : Fin 4) (x t : Fin 7) (hx : x ∈ qa_nb i)
      (nonempty : (r x).Nonempty) (sub : r x ⊆ r t) : t ∈ A i := by
    obtain ⟨k,hk⟩ := nonempty
    have hkx := (Finset.mem_filter.1 hk).2
    have hkt := (Finset.mem_filter.1 (sub hk)).2
    apply Finset.mem_filter.2
    refine ⟨Finset.mem_univ _,?_⟩
    apply equality_residual_co_label h hD b hb pos hpos (line_el x) (line_el t)
      (point_in i) ((qa_geometry.2.2.1 i x).1 hx)
    · intro u hu hux
      obtain ⟨j,rfl⟩ := (onto u).1 hu
      exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩))).2
    · exact ⟨(a k).1,hkx,hkt⟩
  have budget (t : Fin 7) : (qa_consumers A t).card + (if t = 0 then 0 else 1) ≤ 2 + (r t).card := by
    let J : Finset (Fin 14) := (qa_consumers A t).image qa_point
    have hJ : ∀ i ∈ J, i ∈ ineligSet 14 D ∧ qa_line t ∈ supp 14 D (src D (pos i)) := by
      intro i hi
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.1 hi
      exact ⟨point_in k,(Finset.mem_filter.1 (Finset.mem_filter.1 hk).2).2⟩
    have hJcard : J.card = (qa_consumers A t).card :=
      Finset.card_image_of_injective _ qa_point_injective
    by_cases ht : t = 0
    · have bound := equality_assigned_budget h hD b hb pos hpos J hJ
      rw [hJcard,← card t] at bound
      simpa only [ht,ite_true,Nat.add_zero] using bound
    · obtain ⟨z,hz,hedge⟩ := qa_geometry.2.2.2.1 t ht
      have hze : z ∈ eligSet 14 D := by
        by_contra hn
        exact hz (hI ▸ sem_mem_inelig.2 hn)
      have bound := equality_assigned_budget_extra h hD b hb pos hpos J hJ hze hedge
      rw [hJcard,← card t] at bound
      simpa only [ht,ite_false] using bound
  let T : Finset (Fin 7) := (Finset.univ.erase 0).filter (fun t => r t ⊆ r 0)
  let X : Finset (Fin 14) := T.image qa_line
  have hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ qa_line 0 ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → qa_line 0 ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ qa_line 0 ∈ supp 14 D w := by
    intro x hx
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.1 hx
    have ht0 : t ≠ 0 := (Finset.mem_erase.1 (Finset.mem_filter.1 ht).1).1
    have sub : r t ⊆ r 0 := (Finset.mem_filter.1 ht).2
    refine ⟨line_el t,fun eq => ht0 (qa_line_injective eq),?_,?_⟩
    · intro u hu hux
      obtain ⟨j,rfl⟩ := (onto u).1 hu
      exact (Finset.mem_filter.1 (sub (Finset.mem_filter.2 ⟨Finset.mem_univ _,hux⟩))).2
    · obtain ⟨i,hi,h0,hit⟩ := qa_geometry.2.2.2.2 t
      obtain ⟨w,hw⟩ := occurs i hi
      refine ⟨w,?_,?_⟩
      · have member : t ∈ qa_mask D w := by rw [hw]; exact hit
        change t ∈ Finset.univ.filter (fun z => qa_line z ∈ supp 14 D w) at member
        exact (Finset.mem_filter.1 member).2
      · have member : (0 : Fin 7) ∈ qa_mask D w := by rw [hw]; exact h0
        change (0 : Fin 7) ∈ Finset.univ.filter (fun z => qa_line z ∈ supp 14 D w) at member
        exact (Finset.mem_filter.1 member).2
  have hJgeo : ∀ i ∈ ({1,2,3} : Finset (Fin 10)), i.val < 4 ∧
      cf_iota cfL7 i ∉ ({0,1,2,3} : Finset (Fin 14)) ∧
      cf_iota cfL7 i ≠ qa_line 0 ∧ ∀ t : Fin 7, cf_iota cfL7 i ≠ qa_line t := by
    decide +kernel
  have bound := equality_cf_nine_free h hD b hb cf7_good (line_el 0) X hX
    {1,2,3} (by decide) (by
      intro i hi
      obtain ⟨small,no,ne,allne⟩ := hJgeo i hi
      refine ⟨small,?_,ne,?_⟩
      · by_contra hn
        exact no (hI ▸ sem_mem_inelig.2 hn)
      · intro member
        obtain ⟨t,_,eq⟩ := Finset.mem_image.1 member
        exact allne t eq.symm)
  have xcard : X.card = T.card := Finset.card_image_of_injective _ qa_line_injective
  change (ru D b (qa_line 0)).card + X.card + 9 ≤ totalSurplus 14 D at bound
  rw [← card 0,xcard] at bound
  apply qa_residual_impossible S r A allowed (by rw [← missing]; exact supersets 2)
    supersets choices missing budget labels
  change (r 0).card + T.card ≤ 5
  omega
