import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
lemma cutLastVerified : ∀ (n : ℕ) (C : Circuit), FanInTwo C →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
        ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  intro n C fan hasNot
  have splitLast (l : List Gate) (h : ∃ g ∈ l, g.op = GateOp.not) :
      ∃ a g b, l = a ++ g :: b ∧ g.op = GateOp.not ∧
        ∀ k ∈ b, k.op ≠ GateOp.not := by
    induction l with
    | nil => simp at h
    | cons t ts ih =>
      by_cases ht : ∃ g ∈ ts, g.op = GateOp.not
      · obtain ⟨a, g, b, rfl, hg, hb⟩ := ih ht
        exact ⟨t :: a, g, b, rfl, hg, hb⟩
      · obtain ⟨g, hg, hop⟩ := h
        rcases List.mem_cons.mp hg with rfl | hm
        · exact ⟨[], g, ts, rfl, hop, fun k hk he => ht ⟨k, hk, he⟩⟩
        · exact (ht ⟨g, hm, hop⟩).elim
  obtain ⟨a, g, b, eqn, hop, noNot⟩ := splitLast C.gates hasNot
  let P : Circuit := ⟨a, g.inputs.headD (n + a.length)⟩
  let Q : Circuit := ⟨b, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro k hk
    apply fan k
    rw [eqn]
    exact List.mem_append_left _ hk
  · intro k hk
    have mem : k ∈ C.gates := by
      rw [eqn]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hk)
    obtain ⟨op, sz⟩ := fan k mem
    refine ⟨?_, sz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op ⊢
    exact op.elim Or.inl (fun h => Or.inr (h.resolve_right (noNot k hk)))
  · simp [Circuit.size, P, Q, eqn]
    omega
  · intro x
    have lengthW (gs : List Gate) (w : List Bool) :
        ((Circuit.mk gs 0).wires w).length = w.length + gs.length := by
      induction gs generalizing w with
      | nil => simp [Circuit.wires]
      | cons t ts ih =>
        change ((Circuit.mk ts 0).wires (_ ++ [_])).length = _
        rw [ih]
        simp
        omega
    have hlen : (P.wires (List.ofFn x)).length = n + a.length := by
      simpa [P, Circuit.wires] using lengthW a (List.ofFn x)
    have val : g.op.eval (g.inputs.map fun k => (P.wires (List.ofFn x)).getD k false) =
        !P.eval (List.ofFn x) := by
      rw [hop]
      cases hh : g.inputs with
      | nil =>
        simp [GateOp.eval, Circuit.eval, P, hh, List.getD_eq_getElem?_getD]
        change ((P.wires (List.ofFn x))[n + a.length]?).getD false = false
        rw [List.getElem?_eq_none (Nat.le_of_eq hlen)]
        rfl
      | cons i is => simp [GateOp.eval, Circuit.eval, P, hh]
    simpa only [Circuit.eval, Circuit.wires, eqn, List.foldl_append, List.foldl_cons,
      Q, P] using congrArg (fun v => Q.eval (P.wires (List.ofFn x) ++ [v])) val

end PEqualNP.Outside.L_meta_2592_aux
