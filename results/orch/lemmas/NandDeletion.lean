import BypassNand
import AliasPrune

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotInput
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma delete_nand_mask {n : ℕ} (pre post : List Gate) (i : Fin n)
    (wire out : ℕ) (edge f : (Fin n → Bool) → Bool)
    (fan : FanInTwo (⟨pre ++ ⟨GateOp.and, [i.val, wire]⟩ :: post, out⟩ : Circuit))
    (post_mono : ∀ g ∈ post, g.op = GateOp.and ∨ g.op = GateOp.or)
    (mask : ∀ x : Fin n → Bool, (run pre (List.ofFn x)).getD wire false = !(edge x))
    (edge_sound : ∀ x : Fin n → Bool, edge x = true → f x = true)
    (correct : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, [i.val, wire]⟩ :: post, out⟩ (List.ofFn x) = f x) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + 1 = (⟨pre ++ ⟨GateOp.and, [i.val, wire]⟩ :: post, out⟩ : Circuit).size ∧
      NotBracket.notCount D =
        NotBracket.notCount (⟨pre ++ ⟨GateOp.and, [i.val, wire]⟩ :: post, out⟩ : Circuit) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x := by
  refine ⟨AliasPrune.drop n i.val pre post out,
    AliasPrune.drop_fan n i.val pre _ post out fan,
    AliasPrune.drop_size n i.val pre post _ out, ?_, ?_⟩
  · simpa using AliasPrune.drop_notCount n i.val pre post
      ⟨GateOp.and, [i.val, wire]⟩ out
  · intro x
    rw [AliasPrune.drop_eval n i.val pre ⟨GateOp.or, [i.val]⟩ post out
      (by have := i.isLt; omega) (List.ofFn x) (by simp) (by simp [GateOp.eval])]
    exact bypass_nand_mask pre post i wire out edge f post_mono mask edge_sound correct x

end PEqualNP.Outside.L_meta_2592_aux.OneNotInput
