import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl runStep w

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (runStep w g)).length = w.length + (g :: gs).length
    rw [ih]
    simp only [runStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma split_last_not (gs : List Gate) (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ q ∈ post, q.op ≠ GateOp.not := by
  classical
  revert h
  induction gs with
  | nil => intro h; simp at h
  | cons g gs ih =>
    intro h
    by_cases ht : ∃ q ∈ gs, q.op = GateOp.not
    · obtain ⟨pre, q, post, heq, hq, hpost⟩ := ih ht
      refine ⟨g :: pre, q, post, ?_, hq, hpost⟩
      simp [heq]
    · have hg : g.op = GateOp.not := by
        obtain ⟨q, hq, hop⟩ := h
        rcases List.mem_cons.mp hq with heq | hmem
        · simpa [heq] using hop
        · exact (ht ⟨q, hmem, hop⟩).elim
      exact ⟨[], g, gs, rfl, hg, fun q hq hop => ht ⟨q, hq, hop⟩⟩

lemma cut_last_not (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, hgs, hgn, hpost⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have hpre : ∀ q ∈ pre, q ∈ C.gates := by
    intro q hq
    rw [hgs]
    exact List.mem_append_left _ hq
  have hsuf : ∀ q ∈ post, q ∈ C.gates := by
    intro q hq
    rw [hgs]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro q hq
    exact fan q (hpre q hq)
  · intro q hq
    obtain ⟨hop, hlen⟩ := fan q (hsuf q hq)
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (hpost q hq hn).elim
  · change pre.length + post.length + 1 = C.gates.length
    rw [hgs, List.length_append, List.length_cons]
    omega
  · intro x
    let w := run pre (List.ofFn x)
    have hgate : g.op.eval (g.inputs.map fun i => w.getD i false) =
        !P.eval (List.ofFn x) := by
      rw [hgn]
      cases hi : g.inputs with
      | nil =>
        simp only [List.map_nil, GateOp.eval, List.headD_nil]
        have hz : P.eval (List.ofFn x) = false := by
          change (run pre (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false = false
          rw [hi, List.headD_nil]
          apply List.getD_eq_default
          rw [run_length, List.length_ofFn]
        rw [hz]
      | cons i is =>
        simp only [hi, List.map_cons, GateOp.eval, List.headD_cons,
          P, Circuit.eval, Circuit.wires]
        rfl
    change (run C.gates (List.ofFn x)).getD C.output false =
      (run post (w ++ [!P.eval (List.ofFn x)])).getD C.output false
    rw [hgs]
    simp only [run, List.foldl_append, List.foldl_cons]
    change (post.foldl runStep (runStep w g)).getD C.output false = _
    rw [runStep, hgate]

end PEqualNP.Outside.L_meta_2592_aux
