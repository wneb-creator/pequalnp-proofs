namespace component

lemma context_parts_mono (n : ℕ) (gs tail : List Gate) (o : ℕ)
    (h : PEqualNP.MetaComplexity.Monotone2 (oldContext n gs tail o)) :
    PEqualNP.MetaComplexity.Monotone2 ⟨gs, 0⟩ ∧
      PEqualNP.MetaComplexity.Monotone2 ⟨tail, 0⟩ := by
  constructor
  · intro g hg
    have hs := h (shiftGate (n + 1) g) (by
      change shiftGate (n + 1) g ∈
        (boundaryGates (allInputs n) ++ gs.map (shiftGate (n + 1))) ++ tail
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr
        (Or.inr (List.mem_map.mpr ⟨g, hg, rfl⟩)))))
    simpa [shiftGate] using hs
  · intro g hg
    exact h g (List.mem_append.mpr (Or.inr hg))

lemma minimal_boundary_bound (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) (hcore : ClosedCore n gs)
    (houts : ∀ i ∈ outs, i < n + gs.length)
    (hreads : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < oldBoundaryLength n gs →
      InterfaceRead n gs outs rho i)
    (hout : o < oldBoundaryLength n gs → InterfaceRead n gs outs rho o)
    (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit (n + 1) (oldContext n gs tail o)) :
    n ≤ outs.length := by
  obtain ⟨hgm, htm⟩ := context_parts_mono n gs tail o hmin.1
  have hsz := hmin.2 (extractedContext n gs outs tail rho o)
    (extractedContext_mono n gs outs tail rho o hgm htm)
    (component_context_function n gs outs tail rho o hcore houts hreads hout)
  have hcount := context_gate_saving n gs outs tail rho o
  omega

lemma context_preserves_minimality (n : ℕ) (gs : List Gate) (outs : List ℕ) (tail : List Gate)
    (rho : ℕ → ℕ) (o : ℕ) (hcore : ClosedCore n gs)
    (houts : ∀ i ∈ outs, i < n + gs.length)
    (hreads : ∀ g ∈ tail, ∀ i ∈ g.inputs, i < oldBoundaryLength n gs →
      InterfaceRead n gs outs rho i)
    (hout : o < oldBoundaryLength n gs → InterfaceRead n gs outs rho o)
    (hboundary : outs.length ≤ n)
    (hmin : PEqualNP.MetaComplexity.IsMinimalMonoCircuit (n + 1) (oldContext n gs tail o)) :
    PEqualNP.MetaComplexity.IsMinimalMonoCircuit (n + 1)
      (extractedContext n gs outs tail rho o) ∧
      (extractedContext n gs outs tail rho o).size = (oldContext n gs tail o).size := by
  obtain ⟨hgm, htm⟩ := context_parts_mono n gs tail o hmin.1
  have hf := component_context_function n gs outs tail rho o hcore houts hreads hout
  have hm := extractedContext_mono n gs outs tail rho o hgm htm
  have hle := context_no_larger n gs outs tail rho o hboundary
  refine ⟨⟨hm, fun D hD hDf => hle.trans (hmin.2 D hD (hDf.trans hf))⟩,
    Nat.le_antisymm hle (hmin.2 _ hm hf)⟩

end component
