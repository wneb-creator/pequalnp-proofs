import DirectNotTerminal
open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_2592.TerminalNot
lemma repeated_not_child_reduces (n : Nat) (pre post : List Gate) (ins : List Nat)
    (isOr : Bool) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (legal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk (((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) ++
        [⟨if isOr then GateOp.or else GateOp.and, [n + pre.length, n + pre.length]⟩])
        (n + ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post).length)))
    (count : PEqualNP.NotBracket.notCount
      (Circuit.mk (((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) ++
        [⟨if isOr then GateOp.or else GateOp.and, [n + pre.length, n + pre.length]⟩])
        (n + ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post).length)) ≤ 2)
    (computes : ∀ x : Fin n → Bool,
      (Circuit.mk (((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) ++
        [⟨if isOr then GateOp.or else GateOp.and, [n + pre.length, n + pre.length]⟩])
        (n + ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post).length)).eval (List.ofFn x) = f x) :
    ∃ P : Circuit, PEqualNP.MetaComplexity.Monotone2 P ∧
      P.size + 3 ≤ (Circuit.mk (((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) ++
        [⟨if isOr then GateOp.or else GateOp.and, [n + pre.length, n + pre.length]⟩])
        (n + ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post).length)).size ∧
      ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  have prefixLegal : PEqualNP.MetaComplexity.FanInTwo
      (Circuit.mk ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) (n + pre.length)) := by
    intro g hg
    exact legal g (List.mem_append_left _ hg)
  have prefixCount : PEqualNP.NotBracket.notCount
      (Circuit.mk ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) (n + pre.length)) ≤ 2 := by
    unfold PEqualNP.NotBracket.notCount at count ⊢
    simp only [List.filter_append, List.length_append] at count ⊢
    omega
  have prefixComputes : ∀ x : Fin n → Bool,
      (Circuit.mk ((pre ++ [(⟨GateOp.not, ins⟩ : Gate)]) ++ post) (n + pre.length)).eval
        (List.ofFn x) = f x := by
    intro x
    have h := computes x
    cases isOr <;>
      simpa only [Bool.false_eq_true, ite_false, ite_true, output_binary_eval,
        GateOp.eval, List.any_cons, List.all_cons, List.any_nil, List.all_nil,
        Bool.and_true, Bool.or_false, Bool.and_self, Bool.or_self, id_eq] using h
  obtain ⟨P, mono, bound, correct⟩ :=
    not_output_reduces n f bottom top pre ins post prefixLegal prefixCount prefixComputes
  refine ⟨P, mono, ?_, correct⟩
  simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at bound ⊢
  omega

end PEqualNP.Outside.L_meta_2592.TerminalNot
