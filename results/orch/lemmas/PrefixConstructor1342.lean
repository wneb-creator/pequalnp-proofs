import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1342.GenericPrefix

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem closed : ∀ (n : ℕ) (a b c d : Fin n),
    let B : Circuit := ⟨[⟨.or, [a.val,b.val]⟩,⟨.or, [c.val,d.val]⟩,⟨.and, [n,n+1]⟩],n+2⟩
    Monotone2 B ∧ B.size = 3 ∧ ∀ x : Fin n → Bool,
      B.wires (List.ofFn x) = List.ofFn x ++
        [x a || x b, x c || x d, (x a || x b) && (x c || x d)] := by
  intro n a b c d
  refine ⟨by simp [Monotone2], rfl, ?_⟩
  intro x
  generalize hw : List.ofFn x = w
  have len : w.length = n := by rw [← hw]; simp
  have get (i : Fin n) (hi : i.val < w.length) : w[i.val] = x i := by
    subst w
    exact List.getElem_ofFn hi
  simp [Circuit.wires, GateOp.eval, List.getD_eq_getElem?_getD,
    List.getElem?_append, len, get, a.isLt, b.isLt, c.isLt, d.isLt, List.append_assoc]

end PEqualNP.Outside.L_meta_1342.GenericPrefix
