import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.PrefixNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def addNotZero (C : Circuit) : Circuit :=
  ⟨⟨GateOp.not, [0]⟩ :: C.gates, C.output⟩

lemma size_prefix (C : Circuit) : (addNotZero C).size = C.size + 1 := rfl

lemma notCount_prefix (C : Circuit) :
    PEqualNP.NotBracket.notCount (addNotZero C) = PEqualNP.NotBracket.notCount C + 1 := by
  simp [addNotZero, PEqualNP.NotBracket.notCount]

lemma fan_prefix (C : Circuit) (hC : FanInTwo C) : FanInTwo (addNotZero C) := by
  intro g hg
  change g ∈ ⟨GateOp.not, [0]⟩ :: C.gates at hg
  rcases List.mem_cons.mp hg with rfl | hg
  · simp
  · exact hC g hg

lemma wires_prefix (C : Circuit) (x : List Bool) :
    (addNotZero C).wires x = C.wires (x ++ [!(x.getD 0 false)]) := rfl

lemma eval_prefix (C : Circuit) (x : List Bool) :
    (addNotZero C).eval x = C.eval (x ++ [!(x.getD 0 false)]) := rfl

lemma eval_prefix_ofFn (C : Circuit) (x : Fin 10 → Bool) :
    (addNotZero C).eval (List.ofFn x) = C.eval (List.ofFn x ++ [!(x 0)]) := by
  rw [eval_prefix]
  simp [List.getD_eq_getElem?_getD]

lemma transfer_not_floor (k : ℕ) (f : (Fin 10 → Bool) → Bool)
    (floor : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x) →
      k + PEqualNP.NotBracket.notCount D ≤ D.size)
    (C : Circuit) (hC : FanInTwo C)
    (hcompute : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)]) = f x) :
    k + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have hc : ∀ x : Fin 10 → Bool, (addNotZero C).eval (List.ofFn x) = f x := by
    intro x
    rw [eval_prefix_ofFn]
    exact hcompute x
  have hb := floor (addNotZero C) (fan_prefix C hC) hc
  rw [size_prefix, notCount_prefix] at hb
  omega

lemma at_most_one_internal_not (f : (Fin 10 → Bool) → Bool)
    (floor : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = f x) →
      17 + PEqualNP.NotBracket.notCount D ≤ D.size)
    (C : Circuit) (hC : FanInTwo C) (hsize : C.size ≤ 18)
    (hcompute : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)]) = f x) :
    PEqualNP.NotBracket.notCount C ≤ 1 := by
  have hb := transfer_not_floor 17 f floor C hC hcompute
  omega

end PEqualNP.Outside.L_meta_1884.PrefixNot
