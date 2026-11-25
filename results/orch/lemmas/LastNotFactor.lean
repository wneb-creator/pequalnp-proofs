import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma splitLastNot (gs : List Gate)
    (hasNot : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ ps g qs, gs = ps ++ g :: qs ∧ g.op = GateOp.not ∧
      ∀ h ∈ qs, h.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at hasNot
  | cons a gs ih =>
    by_cases tailNot : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨ps, g, qs, split, op, tail⟩ := ih tailNot
      exact ⟨a :: ps, g, qs, by simp [split], op, tail⟩
    · have op : a.op = GateOp.not := by
        obtain ⟨g, mem, op⟩ := hasNot
        rcases List.mem_cons.mp mem with rfl | mem
        · exact op
        · exact (tailNot ⟨g, mem, op⟩).elim
      exact ⟨[], a, gs, rfl, op, fun h mem eq => tailNot ⟨h, mem, eq⟩⟩

lemma wiresLength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  obtain ⟨gs, out⟩ := C
  induction gs generalizing x with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length =
      x.length + (g :: gs).length
    rw [ih]
    simp [Circuit.size, Nat.add_comm, Nat.add_left_comm]

lemma factorLastNot (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨ps, g, qs, split, op, tail⟩ := splitLastNot C.gates hasNot
  let P : Circuit := ⟨ps, g.inputs.headD (n + ps.length)⟩
  let Q : Circuit := ⟨qs, C.output⟩
  have pFan : FanInTwo P := by
    intro h mem
    apply fan h
    rw [split]
    exact List.mem_append_left _ mem
  have qMono : Monotone2 Q := by
    intro h mem
    have hmem : h ∈ C.gates := by
      rw [split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ mem)
    obtain ⟨ops, arity⟩ := fan h hmem
    refine ⟨?_, arity⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ops ⊢
    rcases ops with eq | eq | eq
    · exact Or.inl eq
    · exact Or.inr eq
    · exact (tail h mem eq).elim
  refine ⟨P, Q, pFan, qMono, ?_, ?_⟩
  · simp only [P, Q, Circuit.size, split, List.length_append, List.length_cons]
    omega
  · intro x
    have missing : (P.wires (List.ofFn x)).getD (n + ps.length) false = false := by
      apply List.getD_eq_default
      rw [wiresLength]
      simp [P, Circuit.size]
    have first : (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false).headD false =
        P.eval (List.ofFn x) := by
      change (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false).headD false =
        (P.wires (List.ofFn x)).getD (g.inputs.headD (n + ps.length)) false
      cases ins : g.inputs with
      | nil => simpa only [List.map_nil, List.headD_nil] using missing.symm
      | cons i is => rfl
    unfold Circuit.eval Circuit.wires
    rw [split, List.foldl_append, List.foldl_cons]
    change (Q.wires (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD
        C.output false = _
    rw [op]
    change (Q.wires (P.wires (List.ofFn x) ++
      [!(g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false).headD false])).getD
        C.output false = _
    rw [first]
    rfl

end PEqualNP.Outside.L_meta_2592_aux
