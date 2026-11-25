theorem realizeMono (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = f10 x) :
    ∃ k S, k ≤ C.size ∧ Live false target k S ∧ ∀ a ∈ S, a ∈ initial := by
  have fan : PEqualNP.MetaComplexity.FanInTwo C := by
    intro g hg
    obtain ⟨ho, hl⟩ := legal g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    exact ⟨ho.imp id Or.inl, hl⟩
  have mono : ∀ g ∈ C.gates, isNot g = false := by
    intro g hg
    have ho := (legal g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho
    rcases ho with ho | ho <;> simp [isNot, ho]
  have he : (execute C.gates initial).getD C.output zero = target := by
    apply bit_ext
    intro r
    rw [← b_read, execute_bits _ _ _ (fun g hg => (fan g hg).1)]
    change (C.wires (initial.map (bit r))).getD C.output false = _
    rw [rowInputs]
    exact (computes _).trans (rowTarget r).symm
  have hp : proper target := by unfold proper; decide +kernel
  have out := get_rep (u := false) (execute C.gates initial) C.output
  rw [he] at out
  unfold Repr at out
  rw [nrm_id (show bit 0 target = false by decide +kernel)] at out
  obtain ⟨k, S, hk, run, hs⟩ := extract C.gates initial fan (u := false)
    (fun _ => mono) hp (out.resolve_right (fun h => h hp))
  have ns : initial.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at hs
  exact ⟨k, S, hk.trans List.countP_le_length, run, hs⟩

end Extended

namespace Geometry

lemma pin_mem_iff (a : Extended.Sig) : a ∈ Extended.initial ↔ ∃ i : Fin 10, pin i = a := by
  have h : List.ofFn pin = Extended.initial := by decide +kernel
  rw [← h, List.mem_ofFn]

lemma projected_available_mono (a : Sig) (h : a = zero ∨ a ∈ inputs) :
    Available false (inputs.map observe) (observe a) := by
  rcases h with rfl | ha
  · exact Or.inr (Or.inl ⟨false, by funext r; simp [observe, bit, zero]⟩)
  · exact Or.inl (List.mem_map.mpr ⟨_, ha, rfl⟩)

lemma project_bin_mono (v u : Fin 10) (d : Fin 4) :
    projectV v (Extended.bin d.val (pin v) (pin u)) = zero ∨
      projectV v (Extended.bin d.val (pin v) (pin u)) ∈ inputs := by
  rw [project_bin_commute, project_self, bin_zero_left]
  split_ifs
  · exact Or.inl rfl
  · exact project_pin v u

lemma needed_pin_mono (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live false Extended.target k S)
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

lemma suffix_floor_seventeen_mono (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u)) :
    17 ≤ k := by
  classical
  have hfirst := needed_pin_mono v u d hne run raw
  let front := pin v :: (S.erase (pin v)).toList
  have nd : front.Nodup := by
    apply List.nodup_cons.mpr
    exact ⟨by simp, Finset.nodup_toList _⟩
  have eqS : front.toFinset = S := by
    ext a
    by_cases ha : a = pin v <;> simp [front, ha, hfirst]
  have hrun := Extended.list_run run front nd eqS
  have same : restrictRows (embedV v) (Extended.observe Extended.target) = observe graph := by
    rw [observe_projectV, project_target]
  have roots : supply false (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro a ha
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    rw [observe_projectV]
    rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
    · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
      exact projected_available_mono _ (project_pin v i)
    · exact projected_available_mono _ (project_bin_mono v u d)
  have lower := projected_bound (embedV v) hrun (same ▸ observe_proper graph_proper)
    Reach.start roots (L := 16) (same ▸ nineMonoFloor)
  have charge : 1 ≤ mass ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    have constant : Constant (restrictRows (embedV v) (Extended.observe (pin v))) := by
      rw [observe_projectV, project_self]
      exact ⟨false, by funext r; simp [observe, bit, zero]⟩
    simp [front, mass_cons, cost, constant]
  omega

lemma binary_floor_eighteen {k : ℕ} {S : Finset Extended.Sig}
    (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 18 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := run
    have impossible := raw Extended.target (by simp)
    have hn : Extended.target ∉ Extended.initial := by decide +kernel
    exact False.elim (hn impossible)
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := run
    obtain ⟨v, rfl⟩ := (pin_mem_iff a).mp (raw a (by simp))
    obtain ⟨u, rfl⟩ := (pin_mem_iff b).mp (raw b (by simp))
    have hne : v ≠ u := by intro h; exact hab (congrArg pin h)
    have hfour : d < 4 := by rcases hd with hd | ⟨_, hd⟩ <;> omega
    have hbound := suffix_floor_seventeen_mono v u ⟨d, hfour⟩ hne tail (by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hU
      · exact Or.inr rfl
      · exact Or.inl (raw z (by simp [hU])))
    omega

lemma suffix_floor_eighteen_mono (v u : Fin 10) (d : Fin 4) (hne : v ≠ u)
    (hd : d.val = 0 ∨ d.val = 2)
    {k : ℕ} {S : Finset Extended.Sig} (run : Extended.Live false Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial ∨ a = Extended.bin d.val (pin v) (pin u))
    (hq : Extended.bin d.val (pin v) (pin u) ∈ S)
    (hneq : Extended.bin d.val (pin v) (pin u) ≠ pin v) : 18 ≤ k := by
  classical
  let q := Extended.bin d.val (pin v) (pin u)
  have hfirst := needed_pin_mono v u d hne run raw
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
  have roots : supply false (inputs.map observe)
      ((front.map Extended.observe).map (restrictRows (embedV v))) := by
    intro a ha
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hm
    rw [observe_projectV]
    rcases raw b (eqS ▸ List.mem_toFinset.mpr hb) with horig | rfl
    · obtain ⟨i, rfl⟩ := (pin_mem_iff b).mp horig
      exact projected_available_mono _ (project_pin v i)
    · exact projected_available_mono _ (project_bin_mono v u d)
  have lower := projected_bound (embedV v) hrun (same ▸ observe_proper graph_proper)
    Reach.start roots (L := 16) (same ▸ nineMonoFloor)
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

lemma first_and_floor_nineteen (v u : Fin 10) (hne : v ≠ u)
    {k : ℕ} {U : Finset Extended.Sig}
    (raw : ∀ a ∈ U, a ∈ Extended.initial)
    (fresh : Extended.bin 0 (pin v) (pin u) ∉ insert (pin v) (insert (pin u) U))
    (tail : Extended.Live false Extended.target k (insert (Extended.bin 0 (pin v) (pin u)) U)) :
    19 ≤ k + 1 := by
  have hneq : Extended.bin 0 (pin v) (pin u) ≠ pin v := by
    intro h
    apply fresh
    simp [h]
  have bound := suffix_floor_eighteen_mono v u 0 hne (Or.inl rfl) tail (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | hm
    · exact Or.inr rfl
    · exact Or.inl (raw a hm)) (by simp) hneq
  omega

end Geometry

theorem monotone_size_eighteen (C : Circuit) (legal : PEqualNP.MetaComplexity.Monotone2 C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    18 ≤ C.size := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realizeMono C legal correct
  exact (Geometry.binary_floor_eighteen run raw).trans hk
