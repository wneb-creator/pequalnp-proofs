namespace PEqualNP.Outside.L_meta_2592_aux.GateFirst

lemma initial_index {v : Extended.Sig} (h : v ∈ Extended.initial) :
    ∃ j : Fin 10, v = Extended.initial.getD j.val Extended.zero := by
  obtain ⟨j, hj, hv⟩ := List.mem_iff_getElem.mp h
  refine ⟨⟨j, by simpa [Extended.initial, Extended.pins] using hj⟩, ?_⟩
  rw [List.getD_eq_getElem _ _ hj]
  exact hv.symm

lemma arbitrary_first_tail_floor {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat} (hd : Extended.allowed true d)
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hab : a ≠ b)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U))
    (raw : ∀ v ∈ U, v ∈ Extended.initial) : 16 ≤ k := by
  obtain ⟨i, eqA⟩ := initial_index ha
  obtain ⟨j, eqB⟩ := initial_index hb
  have bound : d < 4 := by unfold Extended.allowed at hd; omega
  let op : Fin 4 := ⟨d, bound⟩
  have remapped := live_rowPerm i tail
  rw [Finset.image_insert, Extended.renameRows_bin, eqA, eqB,
    rowPerm_anchor, rowPerm_input] at remapped
  have distinct : vertexMap i j ≠ 0 := by
    intro same
    have equalImages : Extended.renameRows (rowPerm i) a =
        Extended.renameRows (rowPerm i) b := by
      rw [eqA, eqB, rowPerm_anchor, rowPerm_input, same]
      rfl
    exact hab (Extended.renameRows_inj (rowPerm i) (rowPerm_surjective i) equalImages)
  apply first_live_tail_floor op (vertexMap i j) distinct remapped
  intro v hv
  obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hv
  exact eq ▸ rowPerm_initial i w (raw w hw)

lemma atLeastSeventeen {k S} (h : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) : 17 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hm := raw Extended.target (Finset.mem_singleton_self _)
    have absent : Extended.target ∉ Extended.initial := by decide +kernel
    exact False.elim (absent hm)
  | succ k =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, _, tail⟩ := h
    have ha := raw a (Finset.mem_insert_self _ _)
    have hb := raw b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have ru : ∀ v ∈ U, v ∈ Extended.initial := by
      intro v hv
      exact raw v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
    have floor := arbitrary_first_tail_floor hd ha hb hab tail ru
    omega

lemma binary_floor_seventeen (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 ≤ C.gates.countP (fun g => !Extended.isNot g) := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  exact (atLeastSeventeen run raw).trans hk

lemma not_count_at_most_two (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x)
    (budget : C.gates.length ≤ 19) : C.gates.countP Extended.isNot ≤ 2 := by
  have floor := binary_floor_seventeen C legal computes
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  have complement : (fun a => decide (¬ Extended.isNot a = true)) =
      (fun a => !Extended.isNot a) := by
    funext a
    cases h : Extended.isNot a <;> simp [h]
  rw [complement] at count
  omega


lemma arbitrary_absorbing_tail_floor {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat} (hd : d = 0 ∨ d = 2)
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hab : a ≠ b)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U))
    (raw : ∀ v ∈ U, v ∈ Extended.initial) : 17 ≤ k := by
  obtain ⟨i, eqA⟩ := initial_index ha
  obtain ⟨j, eqB⟩ := initial_index hb
  have bound : d < 4 := by omega
  let op : Fin 4 := ⟨d, bound⟩
  have remapped := live_rowPerm i tail
  rw [Finset.image_insert, Extended.renameRows_bin, eqA, eqB,
    rowPerm_anchor, rowPerm_input] at remapped
  have distinct : vertexMap i j ≠ 0 := by
    intro same
    have equalImages : Extended.renameRows (rowPerm i) a =
        Extended.renameRows (rowPerm i) b := by
      rw [eqA, eqB, rowPerm_anchor, rowPerm_input, same]
      rfl
    exact hab (Extended.renameRows_inj (rowPerm i) (rowPerm_surjective i) equalImages)
  have ho : op = 0 ∨ op = 2 := by
    rcases hd with hd | hd
    · exact Or.inl (Fin.ext hd)
    · exact Or.inr (Fin.ext hd)
  apply first_live_absorbing_floor op (vertexMap i j) ho distinct remapped
  intro v hv
  obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hv
  exact eq ▸ rowPerm_initial i w (raw w hw)

lemma non_or_first_tail_floor {k : Nat} {U : Finset Extended.Sig}
    {a b : Extended.Sig} {d : Nat} (hd : Extended.allowed true d) (nonOr : d ≠ 1)
    (ha : a ∈ Extended.initial) (hb : b ∈ Extended.initial) (hab : a ≠ b)
    (tail : Extended.Live true Extended.target k (insert (Extended.bin d a b) U))
    (raw : ∀ v ∈ U, v ∈ Extended.initial) : 17 ≤ k := by
  have bound : d < 4 := by unfold Extended.allowed at hd; omega
  by_cases last : d = 3
  · have swapped : Extended.bin d a b = Extended.bin 2 b a := by
      rw [last]
      simp [Extended.bin, BitVec.and_comm]
    rw [swapped] at tail
    exact arbitrary_absorbing_tail_floor (Or.inr rfl) hb ha (Ne.symm hab) tail raw
  · exact arbitrary_absorbing_tail_floor (by omega) ha hb hab tail raw

lemma seventeen_requires_or_first {k S} (h : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ Extended.initial) (budget : k ≤ 17) :
    ∃ U a b, k = 17 ∧ S = insert a (insert b U) ∧ a ≠ b ∧
      Extended.Live true Extended.target 16 (insert (Extended.bin 1 a b) U) := by
  have floor := atLeastSeventeen h raw
  have exactSize : k = 17 := by omega
  subst k
  obtain ⟨U, a, b, d, hd, rfl, _, _, hab, _, tail⟩ := h
  have ha := raw a (Finset.mem_insert_self _ _)
  have hb := raw b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ru : ∀ v ∈ U, v ∈ Extended.initial := by
    intro v hv
    exact raw v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv))
  have eq : d = 1 := by
    by_contra hn
    have impossible := non_or_first_tail_floor hd hn ha hb hab tail ru
    omega
  exact ⟨U, a, b, rfl, rfl, hab, eq ▸ tail⟩

end PEqualNP.Outside.L_meta_2592_aux.GateFirst
