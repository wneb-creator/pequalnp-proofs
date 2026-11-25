import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1342.Prefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem closed : ∀ a b c d : Fin 11,
    let B : Circuit := ⟨[⟨.or, [a.val,b.val]⟩,⟨.or, [c.val,d.val]⟩,⟨.and, [11,12]⟩],13⟩
    Monotone2 B ∧ B.size = 3 ∧ ∀ x : Fin 11 → Bool,
      B.wires (List.ofFn x) = List.ofFn x ++
        [x a || x b, x c || x d, (x a || x b) && (x c || x d)] := by
  intro a b c d
  refine ⟨by simp [Monotone2], rfl, ?_⟩
  intro x
  generalize hw : List.ofFn x = w
  have len : w.length = 11 := by rw [← hw]; simp
  have get (i : Fin 11) (hi : i.val < w.length) : w[i.val] = x i := by
    subst w
    fin_cases i <;> rfl
  simp [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
    List.getElem?_append, len, get, a.isLt, b.isLt, c.isLt, d.isLt, List.append_assoc]

end PEqualNP.Outside.L_meta_1342.Prefix
