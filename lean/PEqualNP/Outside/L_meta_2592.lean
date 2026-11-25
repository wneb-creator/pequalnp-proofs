import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gs : List Gate) (hn : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ h ∈ post, h.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at hn
  | cons a gs ih =>
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, he, hop, hm⟩ := ih ht
      exact ⟨a :: pre, g, post, by simp only [he, List.cons_append], hop, hm⟩
    · have ha : a.op = GateOp.not := by
        obtain ⟨g, hg, hop⟩ := hn
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hop
        · exact (ht ⟨g, hg, hop⟩).elim
      exact ⟨[], a, gs, rfl, ha, fun g hg hop => ht ⟨g, hg, hop⟩⟩

lemma wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_singleton, List.length_cons, List.length_nil]
    omega

lemma cut_last_not (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hn : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, he, hop, hpost⟩ := split_last_not C.gates hn
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have hP : FanInTwo P := by
    intro h hh
    exact hf h (he ▸ List.mem_append_left _ hh)
  have hQ : Monotone2 Q := by
    intro h hh
    obtain ⟨ho, hi⟩ := hf h (he ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
    refine ⟨?_, hi⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    rcases ho with ho | ho | ho
    · exact Or.inl ho
    · exact Or.inr ho
    · exact (hpost h hh ho).elim
  refine ⟨P, Q, hP, hQ, ?_, ?_⟩
  · simp only [P, Q, Circuit.size, he, List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      simpa only [P, Circuit.wires, List.length_ofFn] using wires_length pre (List.ofFn x)
    have hv : g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false) =
        !P.eval (List.ofFn x) := by
      rw [hop]
      cases hi : g.inputs with
      | nil =>
        change true = !(P.wires (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false
        rw [hi]
        simp only [List.headD_nil]
        rw [List.getD_eq_default _ _ (by omega)]
        rfl
      | cons i ins =>
        change (!((P.wires (List.ofFn x)).getD i false)) =
          (!((P.wires (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false))
        rw [hi]
        rfl
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [he, List.foldl_append]
    change Q.eval (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false)]) = _
    rw [hv]

end PEqualNP.Outside.L_meta_2592_aux
