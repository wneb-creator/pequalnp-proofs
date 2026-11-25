import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.CircuitLowerBounds

def path4LongGates (k a b c d : ℕ) : List Gate :=
  [⟨.or, [a, c]⟩, ⟨.or, [b, d]⟩, ⟨.and, [k, k + 1]⟩,
    ⟨.or, [b, c]⟩, ⟨.and, [k + 2, k + 3]⟩]

def path4ShortGates (k a b c d : ℕ) : List Gate :=
  [⟨.or, [a, c]⟩, ⟨.and, [b, k]⟩, ⟨.and, [c, d]⟩,
    ⟨.or, [k + 1, k + 2]⟩]

lemma path4_tail_exchange (w : List Bool) (a b c d : Fin w.length) :
    (⟨path4LongGates w.length a b c d, w.length + 4⟩ : Circuit).eval w =
      (⟨path4ShortGates w.length a b c d, w.length + 3⟩ : Circuit).eval w := by
  have old (i : Fin w.length) (t : List Bool) :
      (w ++ t).getD i.val false = w.getD i.val false :=
    List.getD_append _ _ _ _ i.isLt
  have fresh (t : List Bool) (j : ℕ) :
      (w ++ t).getD (w.length + j) false = t.getD j false := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simp only [Nat.add_sub_cancel_left]
    rfl
  have fresh0 (t : List Bool) : (w ++ t).getD w.length false = t.getD 0 false := by
    simpa using fresh t 0
  simp only [Circuit.eval, Circuit.wires, path4LongGates, path4ShortGates,
    List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, Bool.and_true,
    Bool.or_false, id_eq, List.append_assoc, old, fresh, fresh0]
  cases w.getD a.val false <;> cases w.getD b.val false <;>
    cases w.getD c.val false <;> cases w.getD d.val false <;> decide

end PEqualNP.Outside.L_meta_1904
