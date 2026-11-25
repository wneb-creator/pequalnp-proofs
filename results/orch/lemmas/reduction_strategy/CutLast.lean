import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gs : List Gate)
    (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre post : List Gate) (ins : List ℕ),
      gs = pre ++ (⟨GateOp.not, ins⟩ : Gate) :: post ∧
      ∀ g ∈ post, g.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases tail : ∃ t ∈ gs, t.op = GateOp.not
    · obtain ⟨pre, post, ins, e, hn⟩ := ih tail
      exact ⟨g :: pre, post, ins, by simp only [List.cons_append, e], hn⟩
    · obtain ⟨t, ht, hop⟩ := h
      have e : t = g := by
        rcases List.mem_cons.mp ht with e | mem
        · exact e
        · exact (tail ⟨t, mem, hop⟩).elim
      subst t
      refine ⟨[], gs, g.inputs, ?_, ?_⟩
      · cases g with
        | mk op ins => simp only at hop; subst op; rfl
      · intro t ht hop
        exact tail ⟨t, ht, hop⟩

lemma wires_length (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (w ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma cutLast (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, post, ins, split, noNot⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, ins.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply fan g
    rw [split]
    exact List.mem_append_left _ hg
  · intro g hg
    obtain ⟨hop, hlen⟩ := fan g (by
      rw [split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (noNot g hg hn).elim
  · change pre.length + post.length + 1 = C.gates.length
    rw [split]
    simp only [List.length_append, List.length_cons]
    omega
  · intro x
    have operand :
        (ins.map fun i => (P.wires (List.ofFn x)).getD i false).headD false =
          P.eval (List.ofFn x) := by
      cases ins with
      | nil =>
        change false = (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD (n + pre.length) false
        rw [List.getD_eq_default _ _ (by rw [wires_length]; simp)]
      | cons i rest => rfl
    unfold Circuit.eval Circuit.wires
    rw [split, List.foldl_append]
    change (post.foldl _ (P.wires (List.ofFn x) ++
      [GateOp.not.eval (ins.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    simp only [GateOp.eval, operand]
    rfl

end PEqualNP.Outside.L_meta_2592_aux
