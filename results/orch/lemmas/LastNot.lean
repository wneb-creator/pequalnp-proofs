import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gates : List Gate)
    (hasNot : ∃ g ∈ gates, g.op = GateOp.not) :
    ∃ (pre post : List Gate) (g : Gate), gates = pre ++ g :: post ∧
      g.op = GateOp.not ∧ ∀ h ∈ post, h.op ≠ GateOp.not := by
  classical
  induction gates with
  | nil =>
    obtain ⟨g, hg, _⟩ := hasNot
    cases hg
  | cons h tail ih =>
    by_cases ht : ∃ g ∈ tail, g.op = GateOp.not
    · obtain ⟨pre, post, g, heq, hg, hpost⟩ := ih ht
      exact ⟨h :: pre, post, g, by simp [heq], hg, hpost⟩
    · refine ⟨[], tail, h, rfl, ?_, ?_⟩
      · obtain ⟨g, hmem, hg⟩ := hasNot
        rcases List.mem_cons.mp hmem with rfl | hmem
        · exact hg
        · exact (ht ⟨g, hmem, hg⟩).elim
      · intro g hg hop
        exact ht ⟨g, hg, hop⟩

lemma eval_fold_length (gates : List Gate) (x : List Bool) :
    (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
      x.length + gates.length := by
  induction gates generalizing x with
  | nil => simp
  | cons g gates ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_singleton,
      List.length_cons, List.length_nil]
    omega

lemma cut_last_not (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, post, g, heq, hop, hpost⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro h hh
    have hpre : h ∈ pre := hh
    apply fan h
    rw [heq]
    exact List.mem_append_left _ hpre
  · intro h hh
    have hmem : h ∈ post := hh
    have hmemC : h ∈ C.gates := by rw [heq]; simp [hmem]
    obtain ⟨hbasis, hlen⟩ := fan h hmemC
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbasis ⊢
    rcases hbasis with hand | hor | hnot
    · exact Or.inl hand
    · exact Or.inr hor
    · exact (hpost h hmem hnot).elim
  · simp only [P, Q, Circuit.size, heq, List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      simpa [P, Circuit.wires] using eval_fold_length pre (List.ofFn x)
    have hvalue : g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false) =
        !P.eval (List.ofFn x) := by
      rw [hop]
      cases hi : g.inputs with
      | nil =>
        have hout : P.output = n + pre.length := by simp [P, hi]
        have hz : P.eval (List.ofFn x) = false := by
          change (P.wires (List.ofFn x)).getD P.output false = false
          rw [hout, ← hlen]
          simp
        simp [GateOp.eval, hi, hz]
      | cons i rest =>
        have hout : P.output = i := by simp [P, hi]
        simp [GateOp.eval, Circuit.eval, hout, hi]
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [heq, List.foldl_append, List.foldl_cons]
    change (post.foldl _ (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD
      C.output false = _
    rw [hvalue]
    rfl

end PEqualNP.Outside.L_meta_2592
