namespace PEqualNP.Outside.L_meta_2592.Binary17.Geometry

lemma needed_pin (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u)) :
    pin v ∈ S := by
  obtain ⟨a, ha, hd⟩ := Extended.live_row_difference run (witness_target v u d hne)
  rcases raw a ha with horig | heq
  · obtain ⟨i, rfl⟩ := (pin_mem_iff a).mp horig
    by_cases h : i = v
    · simpa [h] using ha
    · exact False.elim (hd (witness_other_pin v u d i h))
  · rw [heq] at hd
    exact False.elim (hd (witness_binary v u d hne))

lemma suffix_floor_seventeen (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    (hd : d.val = 0 ∨ d.val = 2)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u))
    (hq : Extended.bin d.val (pin v) (pin u) ∈ S)
    (hneq : Extended.bin d.val (pin v) (pin u) ≠ pin v) : 17 ≤ k := by
  classical
  let q := Extended.bin d.val (pin v) (pin u)
  have hfirst : pin v ∈ S := needed_pin v u d hne run raw
  let front := pin v :: q :: ((S.erase (pin v)).erase q).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    refine ⟨?_, ?_⟩
    · simp [q, Ne.symm hneq]
    · apply List.nodup_cons.mpr
      exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = pin v <;> by_cases hqa : a = q <;>
      simp [front, ha, hqa, hfirst, hq, q]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (embedV v) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectV, project_target]
  have roots : supply true (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro a ha
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    rw [observe_projectV]
    rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
    · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
      rcases project_pin v i with hz | hm
      · exact projected_available _ (Or.inl hz)
      · exact projected_available _ (Or.inr (Or.inr (Or.inl hm)))
    · exact projected_available _ (project_bin v u d)
  have lower := projected_bound (embedV v) hrun (same ▸ observe_proper graph_proper)
    Reach.start roots (L := 15) (same ▸ nineFloor)
  have cpin : Constant (restrictRows (embedV v) (Extended.observe (pin v))) := by
    rw [observe_projectV, project_self]
    exact ⟨false, by funext r; simp [observe, bit, zero]⟩
  have cq : Constant (restrictRows (embedV v) (Extended.observe q)) := by
    rw [observe_projectV]
    change Constant (observe (projectV v (Extended.bin d.val (pin v) (pin u))))
    rw [project_bin_commute, project_self, bin_zero_left, if_pos hd]
    exact ⟨false, by funext r; simp [observe, bit, zero]⟩
  have charge : 2 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    simp [front, mass_cons, cost, cpin, cq]
    omega
  omega

lemma first_and_floor (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    (hd : d.val = 0 ∨ d.val = 2)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (fresh : Extended.bin d.val (pin v) (pin u) ∉ insert (pin v) (insert (pin u) U))
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d.val (pin v) (pin u)) U)) :
    18 ≤ k + 1 := by
  have hneq : Extended.bin d.val (pin v) (pin u) ≠ pin v := by
    intro h
    apply fresh
    simp [h]
  have bound := suffix_floor_seventeen v u d hne hd tail (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | hm
    · exact Or.inr rfl
    · exact Or.inl (raw a hm)) (by simp) hneq
  omega

lemma first_non_or_floor (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    (hd : d.val ≠ 1)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (fresh : Extended.bin d.val (pin v) (pin u) ∉ insert (pin v) (insert (pin u) U))
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d.val (pin v) (pin u)) U)) :
    18 ≤ k + 1 := by
  fin_cases d
  · exact first_and_floor v u 0 hne (Or.inl rfl) raw fresh tail
  · exact False.elim (hd rfl)
  · exact first_and_floor v u 2 hne (Or.inr rfl) raw fresh tail
  · have eq : Extended.bin 3 (pin v) (pin u) = Extended.bin 2 (pin u) (pin v) := by
      simp [Extended.bin, BitVec.and_comm]
    have fresh' : Extended.bin 2 (pin u) (pin v) ∉ insert (pin u) (insert (pin v) U) := by
      rw [← eq]
      intro hm
      apply fresh
      simpa only [Finset.insert_comm] using hm
    have tail' : Extended.Live true Extended.target k
        (insert (Extended.bin 2 (pin u) (pin v)) U) := by
      simpa only [eq] using tail
    exact first_and_floor u v 2 hne.symm (Or.inr rfl) raw fresh' tail'

end PEqualNP.Outside.L_meta_2592.Binary17.Geometry
