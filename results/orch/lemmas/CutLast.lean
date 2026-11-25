import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2592

lemma split_last_not (gs : List Gate) (hasNot : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre : List Gate) (g : Gate) (post : List Gate),
      gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ h ∈ post, h.op ≠ GateOp.not := by
  induction gs with
  | nil => simp at hasNot
  | cons a gs ih =>
    by_cases later : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, equal, op, last⟩ := ih later
      exact ⟨a :: pre, g, post, by simp [equal], op, last⟩
    · have op : a.op = GateOp.not := by
        obtain ⟨g, member, op⟩ := hasNot
        rcases List.mem_cons.mp member with rfl | member
        · exact op
        · exact (later ⟨g, member, op⟩).elim
      exact ⟨[], a, gs, rfl, op, fun h member eq => later ⟨h, member, eq⟩⟩

lemma fold_wire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w).length =
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
  obtain ⟨pre, g, post, split, op, last⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have preFan : FanInTwo P := by
    intro h member
    apply fan h
    rw [split]
    exact List.mem_append_left _ member
  have postMono : Monotone2 Q := by
    intro h member
    have hfan := fan h (by rw [split]; exact List.mem_append_right _ (List.mem_cons_of_mem _ member))
    refine ⟨?_, hfan.2⟩
    change h.op = GateOp.and ∨ h.op = GateOp.or
    have allowed := hfan.1
    change h.op = GateOp.and ∨ h.op = GateOp.or ∨ h.op = GateOp.not at allowed
    rcases allowed with hand | hor | hnot
    · exact Or.inl hand
    · exact Or.inr hor
    · exact (last h member hnot).elim
  refine ⟨P, Q, preFan, postMono, ?_, ?_⟩
  · change pre.length + post.length + 1 = C.gates.length
    rw [split]
    simp [Nat.add_assoc]
  · intro x
    let w := P.wires (List.ofFn x)
    have length : w.length = n + pre.length := by
      dsimp only [w, P, Circuit.wires]
      rw [fold_wire_length, List.length_ofFn]
    have value : g.op.eval (g.inputs.map fun i => w.getD i false) = !P.eval (List.ofFn x) := by
      change g.op.eval (g.inputs.map fun i => w.getD i false) =
        !(w.getD (g.inputs.headD (n + pre.length)) false)
      cases inputs : g.inputs with
      | nil =>
        simp only [op, List.map_nil, GateOp.eval, List.headD_nil, Bool.not_false]
        rw [List.getD_eq_default _ _ (by omega)]
        rfl
      | cons i rest => simp [op, GateOp.eval]
    rw [Circuit.eval, Circuit.wires, split]
    change ((pre ++ g :: post).foldl
      (fun v h => v ++ [h.op.eval (h.inputs.map fun i => v.getD i false)]) (List.ofFn x)).getD
        C.output false = Q.eval (w ++ [!P.eval (List.ofFn x)])
    rw [List.foldl_append, List.foldl_cons]
    change (post.foldl (fun v h => v ++ [h.op.eval (h.inputs.map fun i => v.getD i false)])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD C.output false = _
    rw [value]
    rfl

end PEqualNP.Outside.L_meta_2592
