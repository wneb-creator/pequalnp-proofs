theorem q5_singleton_impossible {r : Fin 6 → Finset (Fin 3)}
    (hr : r 0 = {0}) (hc : q5_constraints r) : False := by
  obtain ⟨a,ha⟩ := q5_mask_surjective (r 1)
  obtain ⟨b,hb⟩ := q5_mask_surjective (r 2)
  obtain ⟨c,hc'⟩ := q5_mask_surjective (r 3)
  obtain ⟨d,hd⟩ := q5_mask_surjective (r 4)
  obtain ⟨e,he⟩ := q5_mask_surjective (r 5)
  have eq : ![q5_mask 1,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] = r := by
    funext t
    fin_cases t <;> simp [q5_mask,hr,← ha,← hb,← hc',← hd,← he]
  exact q5_singleton_certificate a b c d e (by simpa only [eq] using hc)

theorem q5_pair_full {r : Fin 6 → Finset (Fin 3)}
    (hr : r 0 = {0,1}) (hc : q5_constraints r) : r 5 = Finset.univ := by
  obtain ⟨a,ha⟩ := q5_mask_surjective (r 1)
  obtain ⟨b,hb⟩ := q5_mask_surjective (r 2)
  obtain ⟨c,hc'⟩ := q5_mask_surjective (r 3)
  obtain ⟨d,hd⟩ := q5_mask_surjective (r 4)
  obtain ⟨e,he⟩ := q5_mask_surjective (r 5)
  have eq : ![q5_mask 3,q5_mask a,q5_mask b,q5_mask c,q5_mask d,q5_mask e] = r := by
    funext t
    fin_cases t <;> simp [q5_mask,hr,← ha,← hb,← hc',← hd,← he]
  have seven := q5_pair_certificate a b c d e (by simpa only [eq] using hc)
  subst e
  rw [← he]
  decide +kernel
