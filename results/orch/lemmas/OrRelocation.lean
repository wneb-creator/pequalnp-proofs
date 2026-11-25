import BypassOr
import AliasPrune

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotInput
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma move_or_mask_same_size {n : ℕ} (pre post : List Gate) (i : Fin n)
    (wire out : ℕ) (wire_back : wire < n + pre.length)
    (edge f : (Fin n → Bool) → Bool)
    (fan : FanInTwo (⟨pre ++ ⟨GateOp.or, [i.val, wire]⟩ :: post, out⟩ : Circuit))
    (mask : ∀ x : Fin n → Bool, (run pre (List.ofFn x)).getD wire false = edge x)
    (edge_sound : ∀ x : Fin n → Bool, edge x = true → f x = true)
    (correct : ∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, [i.val, wire]⟩ :: post, out⟩ (List.ofFn x) = f x) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size = (⟨pre ++ ⟨GateOp.or, [i.val, wire]⟩ :: post, out⟩ : Circuit).size ∧
      NotBracket.notCount D =
        NotBracket.notCount (⟨pre ++ ⟨GateOp.or, [i.val, wire]⟩ :: post, out⟩ : Circuit) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x := by
  let final : Gate := ⟨GateOp.or, [out, wire]⟩
  let finalOut : ℕ := n + (pre ++ ⟨GateOp.or, [i.val]⟩ :: post).length
  refine ⟨AliasPrune.drop n i.val pre (post ++ [final]) finalOut, ?_, ?_, ?_, ?_⟩
  · apply AliasPrune.drop_fan n i.val pre ⟨GateOp.or, [i.val, wire]⟩ (post ++ [final]) finalOut
    intro g hg
    have split : g ∈ pre ++ ⟨GateOp.or, [i.val, wire]⟩ :: post ∨ g = final := by
      simpa [List.mem_append, List.mem_cons, or_assoc] using hg
    rcases split with hg | rfl
    · exact fan g hg
    · exact ⟨by simp [final], by simp [final]⟩
  · simp [AliasPrune.drop, Circuit.size, final]
  · have hn := AliasPrune.drop_notCount n i.val pre (post ++ [final])
      ⟨GateOp.or, [i.val]⟩ finalOut
    simpa [NotBracket.notCount, List.filter_append, final] using hn
  · intro x
    rw [AliasPrune.drop_eval n i.val pre ⟨GateOp.or, [i.val]⟩ (post ++ [final]) finalOut
      (by have := i.isLt; omega) (List.ofFn x) (by simp) (by simp [GateOp.eval])]
    have h := move_or_mask_to_output pre post i wire out wire_back edge f mask edge_sound correct x
    simpa only [Circuit.size, List.append_assoc, List.cons_append, final, finalOut] using h

end PEqualNP.Outside.L_meta_2592_aux.OneNotInput
