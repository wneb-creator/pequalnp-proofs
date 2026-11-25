import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2592_aux

lemma split_last_not (gs : List Gate)
    (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ q ∈ post, q.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simpa using h
  | cons a gs ih =>
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, heq, hop, hpost⟩ := ih ht
      exact ⟨a :: pre, g, post, by simp [heq], hop, hpost⟩
    · refine ⟨[], a, gs, rfl, ?_, ?_⟩
      · obtain ⟨g, hg, hop⟩ := h
        rcases List.mem_cons.mp hg with heq | hmem
        · simpa [heq] using hop
        · exact (ht ⟨g, hmem, hop⟩).elim
      · intro q hq hop
        exact ht ⟨q, hq, hop⟩

lemma wires_length (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma cut_last_not (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hn : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, heq, hop, hpost⟩ := split_last_not C.gates hn
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have hp : FanInTwo P := by
    intro q hq
    apply hf q
    rw [heq]
    exact List.mem_append_left _ hq
  have hq : Monotone2 Q := by
    intro q hq
    have hmem : q ∈ C.gates := by
      rw [heq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
    obtain ⟨hbasis, hlen⟩ := hf q hmem
    refine ⟨?_, hlen⟩
    rcases hbasis with hand | hor | hnot
    · exact Or.inl hand
    · exact Or.inr hor
    · exact (hpost q hq hnot).elim
  refine ⟨P, Q, hp, hq, ?_, ?_⟩
  · simp [P, Q, Circuit.size, heq]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      change (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).length = _
      rw [wires_length]
      simp
    have hv : g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false) = !P.eval (List.ofFn x) := by
      rw [hop]
      cases hi : g.inputs with
      | nil =>
        have hd : (P.wires (List.ofFn x)).getD (n + pre.length) false = false :=
          List.getD_eq_default _ _ (by omega)
        simpa [GateOp.eval, Circuit.eval, P, hi] using congrArg Bool.not hd.symm
      | cons j js => simp [GateOp.eval, Circuit.eval, P, hi]
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false =
      (post.foldl _ (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)])).getD C.output false
    rw [heq, List.foldl_append, List.foldl_cons]
    change (post.foldl _ (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD
      C.output false = _
    rw [hv]

end PEqualNP.Outside.L_meta_2592_aux
