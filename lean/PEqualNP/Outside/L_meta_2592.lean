import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma last_not_split (gs : List Gate) :
    (∃ g ∈ gs, g.op = GateOp.not) →
    ∃ (pre : List Gate) (g : Gate) (post : List Gate),
      gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ t ∈ post, t.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil =>
    rintro ⟨g, hg, _⟩
    cases hg
  | cons a gs ih =>
    intro h
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, heq, hnot, hpost⟩ := ih ht
      exact ⟨a :: pre, g, post, by simp [heq], hnot, hpost⟩
    · refine ⟨[], a, gs, rfl, ?_, ?_⟩
      · obtain ⟨g, hg, hn⟩ := h
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hn
        · exact False.elim (ht ⟨g, hg, hn⟩)
      · intro t ht' hn
        exact ht ⟨t, ht', hn⟩

lemma run_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma last_not_cut (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, hsplit, hg, hpost⟩ := last_not_split C.gates hnot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have pre_mem (t : Gate) (ht : t ∈ pre) : t ∈ C.gates := by
    rw [hsplit]
    exact List.mem_append_left _ ht
  have post_mem (t : Gate) (ht : t ∈ post) : t ∈ C.gates := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hfan t (pre_mem t ht)
  · intro t ht
    obtain ⟨hop, hlen⟩ := hfan t (post_mem t ht)
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact False.elim (hpost t ht hop)
  · change pre.length + post.length + 1 = C.gates.length
    rw [hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      have h := run_length pre (List.ofFn x)
      simpa only [P, Circuit.wires, List.length_ofFn] using h
    have hvalue : g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false) = !P.eval (List.ofFn x) := by
      rw [hg]
      cases hinputs : g.inputs with
      | nil =>
        change true = !((P.wires (List.ofFn x)).getD P.output false)
        have hout : P.output = n + pre.length := by simp [P, hinputs]
        rw [hout, ← hlen, List.getD_eq_default _ _ (by omega)]
        rfl
      | cons a rest =>
        change (!((P.wires (List.ofFn x)).getD a false)) =
          (!((P.wires (List.ofFn x)).getD P.output false))
        have hout : P.output = a := by simp [P, hinputs]
        rw [hout]
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [hsplit, List.foldl_append]
    change (post.foldl _ (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    rw [hvalue]
    rfl

end PEqualNP.Outside.L_meta_2592
