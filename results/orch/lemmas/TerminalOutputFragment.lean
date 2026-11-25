lemma wf_preserves (tail : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (wf tail w).getD i false = w.getD i false := by
  induction tail generalizing w with
  | nil => rfl
  | cons g tail ih =>
    rw [wf_cons, ih _ (by simp; omega), getD_snoc_lt _ _ _ hi]

lemma appended_eval (gs tail : List Gate) (out : Nat) (w : List Bool)
    (bound : out < w.length + gs.length) :
    (Circuit.mk (gs ++ tail) out).eval w = (Circuit.mk gs out).eval w := by
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  exact wf_preserves tail (wf gs w) out (by rw [wf_len]; exact bound)

lemma not_output_reduces (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (gs : List Gate) (ins : List Nat) (tail : List Gate)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)) ≤ 2)
    (computes : ∀ x : Fin n → Bool,
      (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)).eval
        (List.ofFn x) = f x) :
    ∃ P : Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 2 ≤ (Circuit.mk ((gs ++ [⟨GateOp.not, ins⟩]) ++ tail) (n + gs.length)).size ∧
      ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  have prefixFan : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) := by
    intro g hg
    exact legal g (List.mem_append_left _ hg)
  have prefixCount : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) ≤ 2 := by
    unfold PEqualNP.NotBracket.notCount at count ⊢
    simp only [List.filter_append, List.length_append] at count ⊢
    omega
  have prefixPos : 1 ≤ PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) := by
    simp [PEqualNP.NotBracket.notCount, List.filter_append]
  have prefixComputes : ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)).eval (List.ofFn x) = f x := by
    intro x
    have preserved := appended_eval (gs ++ [⟨GateOp.not, ins⟩]) tail (n + gs.length)
      (List.ofFn x) (by simp)
    exact preserved.symm.trans (computes x)
  have cases : PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 1 ∨
      PEqualNP.NotBracket.notCount
      (Circuit.mk (gs ++ [⟨GateOp.not, ins⟩]) (n + gs.length)) = 2 := by omega
  rcases cases with h | h
  · exact False.elim (single_not_output_impossible n f bottom top gs ins prefixFan h prefixComputes)
  · obtain ⟨P, mono, budget, correct⟩ :=
      two_not_output_reduces n f bottom top gs ins prefixFan h prefixComputes
    refine ⟨P, mono, budget.trans ?_, correct⟩
    simp [Circuit.size, List.length_append]
