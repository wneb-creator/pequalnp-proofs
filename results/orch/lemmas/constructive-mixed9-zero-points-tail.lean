theorem equality_m9_zero_points_of_certificate
    (certificate : ∀ (r : Fin 6 → Fin 8) (a b : Fin 3) (T : Fin 8),
      (r 0 = 1 ∨ r 0 = 3) → m9_normal r a b = true → m9_pointAllowed r a b T = false)
    {D : Dag} (h : StrictLive 14 D) (hD : Correct D) (h14 : totalSurplus 14 D ≤ 14)
    (b : Fin 14 → ℕ) (hb : PureBranch 14 D b)
    (hI : ineligSet 14 D = {0,1,2,5,11})
    (missing2 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 2))
    (missing5 : ¬ sup_Occ 14 D mx_L (sem_hw_nb 5))
    (protects : ∀ i ∈ ({0,1} : Finset (Fin 14)), ∀ w,
      Relation.ReflTransGen (sem_step 14 D) i.val w → fanout D w ≤ 1)
    (a : Fin 3 → (Σ _ : ℕ, ℕ)) (injective : Function.Injective a)
    (onto : ∀ u, u ∈ residualUnits 14 D b ↔ ∃ k, a k = u)
    (first : equality_coordinate_set (D := D) a 7 = {0} ∨
      equality_coordinate_set (D := D) a 7 = {0,1}) :
    ∀ z ∈ ({3,4,6} : Finset (Fin 14)), ru D b z = ∅ := by
  classical
  obtain ⟨α,β,normal,points⟩ := equality_m9_all_constraints h hD h14 b hb hI
    missing2 missing5 protects a injective onto
  intro z hz
  have zero : equality_coordinate_set (D := D) a z = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro k member
    have positive : (equality_coordinate_set (D := D) a z).Nonempty := ⟨k,member⟩
    exact m9_no_point_constraints_of_certificate certificate
      (fun t => equality_coordinate_set (D := D) a (equality_m9_line t)) α β
      (equality_coordinate_set (D := D) a z) first normal (points z hz positive)
  have card := equality_coordinate_card a injective onto z
  rw [zero,Finset.card_empty] at card
  exact Finset.card_eq_zero.1 card.symm
