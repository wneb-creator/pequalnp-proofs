namespace PEqualNP.Outside.L_meta_6659_aux

theorem equality_cf_nine_free {D : Dag} (h : StrictLive 14 D) (hD : Correct D)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b) {c : Fin 14} {l : List ℕ}
    (hgood : cf_good c l) (hc : c ∈ eligSet 14 D) (X : Finset (Fin 14))
    (hX : ∀ x ∈ X, x ∈ eligSet 14 D ∧ x ≠ c ∧
      (∀ u ∈ residualUnits 14 D b, x ∈ supp 14 D u.1 → c ∈ supp 14 D u.1) ∧
      ∃ w, x ∈ supp 14 D w ∧ c ∈ supp 14 D w)
    (J : Finset (Fin 10)) (hJcard : 3 ≤ J.card)
    (hJ : ∀ i ∈ J, i.val < 4 ∧ cf_iota l i ∈ eligSet 14 D ∧
      cf_iota l i ≠ c ∧ cf_iota l i ∉ X) :
    (ru D b c).card + X.card + 9 ≤ totalSurplus 14 D := by
  classical
  obtain ⟨E,hE,hCE,hbound,_,_,hextra⟩ := equality_cf_main_many h hD b hb hgood hc X hX
  by_cases h6 : totalSurplus 10 E ≤ 6
  · have hel := k4_equality_eligible hE hCE h6
    have hin : ∀ i ∈ J, i ∈ ineligSet 10 E := by
      intro i hi
      apply sem_mem_inelig.mpr
      rw [hel]
      have hv := (hJ i hi).1
      fin_cases i <;> simp_all
    have hx := hextra J (fun i hi => ⟨hin i hi,(hJ i hi).2⟩)
    have hmin := k4_surplus_six hE hCE
    have hle := Bplus_le_total 10 E
    omega
  · by_cases h7 : totalSurplus 10 E ≤ 7
    · have htwo := ke_at_most_two_originals hE hCE h7
      have exists_ineligible : ∃ i ∈ J, i ∈ ineligSet 10 E := by
        by_contra hn
        have sub : J ⊆ ({0,1,2,3} : Finset (Fin 10)) ∩ eligSet 10 E := by
          intro i hi
          refine Finset.mem_inter.mpr ⟨?_,?_⟩
          · have hv := (hJ i hi).1
            fin_cases i <;> simp_all
          · by_contra hne
            exact hn ⟨i,hi,sem_mem_inelig.mpr hne⟩
        have card := Finset.card_le_card sub
        omega
      obtain ⟨i,hi,hin⟩ := exists_ineligible
      have hx := hextra {i} (by
        intro j hj
        have ji := Finset.mem_singleton.mp hj
        subst j
        exact ⟨hin,(hJ i hi).2⟩)
      rw [Finset.card_singleton] at hx
      omega
    · omega

end PEqualNP.Outside.L_meta_6659_aux
