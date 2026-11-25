lemma first_binary_swap_eval (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ)
    (tail : List Gate) (output : ℕ) (x : List Bool) :
    (Circuit.mk (Gate.mk op [a, b] :: tail) output).eval x =
      (Circuit.mk (Gate.mk op [b, a] :: tail) output).eval x := by
  have hopEq : ∀ s t : Bool, op.eval [s, t] = op.eval [t, s] := by
    rcases hop with rfl | rfl <;> intro s t <;>
      simp [GateOp.eval, Bool.and_comm, Bool.or_comm]
  simp only [Circuit.eval, Circuit.wires, List.foldl_cons, List.map_cons, List.map_nil]
  rw [hopEq]

lemma first_binary_reuses_both (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (i j : Fin 10) (hij : i ≠ j)
    (tail : List Gate) (output : ℕ)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (Gate.mk op [i.val, j.val] :: tail) output).eval (List.ofFn x) = searchEdge x) :
    (∃ g ∈ tail, i.val ∈ g.inputs) ∧ (∃ g ∈ tail, j.val ∈ g.inputs) := by
  refine ⟨first_binary_reuses_input op hop i j hij tail output computes, ?_⟩
  apply first_binary_reuses_input op hop j i (Ne.symm hij) tail output
  intro x
  rw [first_binary_swap_eval op hop j.val i.val tail output]
  exact computes x
