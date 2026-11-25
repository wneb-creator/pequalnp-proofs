import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not {gs : List Gate}
    (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ q ∈ post, q.op ≠ GateOp.not := by
  induction gs with
  | nil => simp at h
  | cons a gs ih =>
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, heq, hg, hpost⟩ := ih ht
      refine ⟨a :: pre, g, post, ?_, hg, hpost⟩
      simp only [List.cons_append, heq]
    · refine ⟨[], a, gs, rfl, ?_, ?_⟩
      · obtain ⟨g, hm, hg⟩ := h
        rcases List.mem_cons.mp hm with ha | hm
        · simpa [ha] using hg
        · exact (ht ⟨g, hm, hg⟩).elim
      · intro q hq hop
        exact ht ⟨q, hq, hop⟩

lemma fold_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma cut_last_not (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, heq, hg, hpost⟩ := split_last_not hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact fan a (by rw [heq]; exact List.mem_append_left _ ha)
  · intro a ha
    have hf := fan a (by rw [heq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))
    refine ⟨?_, hf.2⟩
    have hn := hpost a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
    rcases hf.1 with hand | hor | hnot
    · exact Or.inl hand
    · exact Or.inr hor
    · exact (hn hnot).elim
  · simp only [Circuit.size, P, Q, heq, List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      simp only [Circuit.wires, P, fold_wires_length, List.length_ofFn]
    have hgate : g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false) = !P.eval (List.ofFn x) := by
      rw [hg]
      cases hi : g.inputs with
      | nil =>
        have hd : (P.wires (List.ofFn x)).getD (n + pre.length) false = false :=
          List.getD_eq_default _ _ (by rw [hlen])
        change GateOp.not.eval _ =
          !((P.wires (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false)
        simp only [hi, List.map_nil, GateOp.eval, List.headD_nil, hd, Bool.not_false]
      | cons i is => simp [GateOp.eval, Circuit.eval, P, hi]
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD C.output false = _
    rw [heq, List.foldl_append, List.foldl_cons]
    change (post.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (P.wires (List.ofFn x) ++ [g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    rw [hgate]
    rfl

end PEqualNP.Outside.L_meta_2592
