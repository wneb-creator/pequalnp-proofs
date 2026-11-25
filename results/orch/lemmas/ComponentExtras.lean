namespace component

lemma boundary_mono (outs : List ℕ) (o : ℕ) :
    PEqualNP.MetaComplexity.Monotone2 ⟨boundaryGates outs, o⟩ := by
  intro g hg
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hg
  simp

lemma shift_mono (gs : List Gate) (d o : ℕ)
    (h : PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩) :
    PEqualNP.MetaComplexity.Monotone2 ⟨gs.map (shiftGate d), o⟩ := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  simpa [shiftGate] using h a ha

lemma append_mono (a b : List Gate) (o : ℕ)
    (ha : PEqualNP.MetaComplexity.Monotone2 ⟨a, 0⟩)
    (hb : PEqualNP.MetaComplexity.Monotone2 ⟨b, 0⟩) :
    PEqualNP.MetaComplexity.Monotone2 ⟨a ++ b, o⟩ := by
  intro g hg
  exact (List.mem_append.mp hg).elim (ha g) (hb g)

lemma joinedBlock_mono (n : ℕ) (gs : List Gate) (o : ℕ)
    (h : PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩) :
    PEqualNP.MetaComplexity.Monotone2 ⟨joinedBlock n gs, o⟩ :=
  append_mono _ _ o (boundary_mono _ 0) (shift_mono gs (n + 1) 0 h)

lemma extractedBlock_mono (gs : List Gate) (outs : List ℕ) (o : ℕ)
    (h : PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩) :
    PEqualNP.MetaComplexity.Monotone2 ⟨extractedBlock gs outs, o⟩ :=
  append_mono _ _ o (shift_mono gs 1 0 h) (boundary_mono _ 0)

lemma component_output (gs : List Gate) (outs : List ℕ) (u : Bool) (x : List Bool)
    (hcore : ClosedCore x.length gs)
    (houts : ∀ i ∈ outs, i < x.length + gs.length) (j : ℕ) (hj : j < outs.length) :
    (wf (extractedBlock gs outs) (u :: x)).getD (x.length + 1 + gs.length + j) false =
      (wf (joinedBlock x.length gs) (u :: x)).getD (x.length + 1 + outs[j]) false := by
  rw [component_extraction gs outs u x hcore houts]
  have hlen : (u :: wf gs x).length = x.length + 1 + gs.length := by
    simp [wf_len]
    omega
  rw [← hlen, getD_shift]
  simp [List.getD_eq_getElem?_getD, hj]

lemma single_output_extraction (gs : List Gate) (o : ℕ) (u : Bool) (x : List Bool)
    (hcore : ClosedCore x.length gs) (hout : o < x.length + gs.length) :
    Circuit.eval ⟨extractedBlock gs [o], x.length + 1 + gs.length⟩ (u :: x) =
      Circuit.eval ⟨joinedBlock x.length gs, x.length + 1 + o⟩ (u :: x) := by
  exact component_output gs [o] u x hcore (by simpa) 0 (by simp)

lemma single_output_gate_saving (gs : List Gate) (o n : ℕ) :
    (extractedBlock gs [o]).length + n = (joinedBlock n gs).length + 1 := by
  simpa using component_gate_saving gs [o] n

end component
