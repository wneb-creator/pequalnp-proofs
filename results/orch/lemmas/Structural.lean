import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma splitLastNot (gs : List Gate) (hn : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre : List Gate) (ins : List ℕ) (post : List Gate),
      gs = pre ++ ({ op := GateOp.not, inputs := ins } : Gate) :: post ∧
      ∀ g ∈ post, g.op ≠ GateOp.not := by
  induction gs with
  | nil => simp at hn
  | cons g gs ih =>
    by_cases ht : ∃ h ∈ gs, h.op = GateOp.not
    · obtain ⟨pre, ins, post, heq, hfree⟩ := ih ht
      refine ⟨g :: pre, ins, post, ?_, hfree⟩
      simp only [List.cons_append, heq]
    · obtain ⟨h, hh, hop⟩ := hn
      rcases List.mem_cons.mp hh with rfl | hh
      · refine ⟨[], g.inputs, gs, ?_, ?_⟩
        · cases g with
          | mk op ins => cases hop; rfl
        · intro h hh hop
          exact ht ⟨h, hh, hop⟩
      · exact (ht ⟨h, hh, hop⟩).elim

lemma wiresLength (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length := by
  cases C with
  | mk gs output =>
    simp only [Circuit.wires]
    induction gs generalizing x with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, List.length_append, List.length_singleton,
        List.length_cons]
      omega

lemma cutLast (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, ins, post, heq, hfree⟩ := splitLastNot C.gates hasNot
  let P : Circuit := ⟨pre, ins.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have pFan : FanInTwo P := by
    intro g hg
    apply fan g
    rw [heq]
    exact List.mem_append_left _ hg
  have qMono : Monotone2 Q := by
    intro g hg
    have hmem : g ∈ C.gates := by
      rw [heq]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg)
    obtain ⟨hop, hlen⟩ := fan g hmem
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hfree g hg h).elim
  refine ⟨P, Q, pFan, qMono, ?_, ?_⟩
  · simp only [Circuit.size, P, Q, heq, List.length_append, List.length_cons]
    omega
  · intro x
    have hvalue : GateOp.not.eval
        (ins.map fun i => (P.wires (List.ofFn x)).getD i false) =
        !P.eval (List.ofFn x) := by
      cases ins with
      | nil =>
        have hdefault : (P.wires (List.ofFn x)).getD (n + pre.length) false = false := by
          apply List.getD_eq_default
          simp only [wiresLength, List.length_ofFn, P]
          exact le_rfl
        change true = !((P.wires (List.ofFn x)).getD (n + pre.length) false)
        rw [hdefault]
        rfl
      | cons i tail => rfl
    change (C.gates.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD C.output false = _
    rw [heq, List.foldl_append, List.foldl_cons]
    change (post.foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (P.wires (List.ofFn x) ++ [GateOp.not.eval
        (ins.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    rw [hvalue]
    rfl

end PEqualNP.Outside.L_meta_2592
