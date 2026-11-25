import TwoNotPair
import DirectNotTerminal
open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_2592.TerminalNot
lemma eval_after_not (pre post : List Gate) (ins : List Nat) (out n : Nat)
    (x : Fin n → Bool) :
    (Circuit.mk (pre ++ ⟨GateOp.not, ins⟩ :: post) out).eval (List.ofFn x) =
      (Circuit.mk post out).eval
        ((Circuit.mk pre (ins.headD (n + pre.length))).wires (List.ofFn x) ++
          [!(Circuit.mk pre (ins.headD (n + pre.length))).eval (List.ofFn x)]) := by
  change (wf (pre ++ ⟨GateOp.not, ins⟩ :: post) (List.ofFn x)).getD out false = _
  rw [insert_not_wires]
  rfl

lemma two_not_output_children_impossible (n : Nat) (pre mid post : List Gate)
    (first second : List Nat) (isOr reverse : Bool)
    (f : (Fin n → Bool) → Bool)
    (preMono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (midMono : ∀ g ∈ mid, g.op = GateOp.and ∨ g.op = GateOp.or)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true) :
    ¬ ∀ x : Fin n → Bool,
      (Circuit.mk
        (((pre ++ ⟨GateOp.not, first⟩ :: mid) ++ ⟨GateOp.not, second⟩ :: post) ++
          [⟨if isOr then GateOp.or else GateOp.and,
            if reverse then [n + (pre ++ ⟨GateOp.not, first⟩ :: mid).length, n + pre.length]
            else [n + pre.length, n + (pre ++ ⟨GateOp.not, first⟩ :: mid).length]⟩])
        (n + ((pre ++ ⟨GateOp.not, first⟩ :: mid) ++ ⟨GateOp.not, second⟩ :: post).length)).eval
          (List.ofFn x) = f x := by
  intro computes
  let P := Circuit.mk pre (first.headD (n + pre.length))
  let Q := Circuit.mk mid (second.headD (n + (pre ++ ⟨GateOp.not, first⟩ :: mid).length))
  apply two_not_pair_impossible n P Q f isOr preMono midMono bottom top
  intro x
  have firstValue :
      (Circuit.mk ((pre ++ ⟨GateOp.not, first⟩ :: mid) ++ ⟨GateOp.not, second⟩ :: post)
        (n + pre.length)).eval (List.ofFn x) = Bool.not (P.eval (List.ofFn x)) := by
    rw [List.append_assoc]
    exact read_internal_not pre (mid ++ ⟨GateOp.not, second⟩ :: post) first n x
  have secondValue :
      (Circuit.mk ((pre ++ ⟨GateOp.not, first⟩ :: mid) ++ ⟨GateOp.not, second⟩ :: post)
        (n + (pre ++ ⟨GateOp.not, first⟩ :: mid).length)).eval (List.ofFn x) =
        Bool.not (Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)])) := by
    rw [read_internal_not, eval_after_not]
  have h := computes x
  cases isOr <;> cases reverse <;>
    simpa only [Bool.false_eq_true, ite_false, ite_true, output_binary_eval,
      firstValue, secondValue, GateOp.eval, List.any_cons, List.all_cons,
      List.any_nil, List.all_nil, Bool.and_true, Bool.or_false, Bool.true_and,
      Bool.false_or, id_eq, Bool.and_comm, Bool.or_comm] using h

end PEqualNP.Outside.L_meta_2592.TerminalNot
