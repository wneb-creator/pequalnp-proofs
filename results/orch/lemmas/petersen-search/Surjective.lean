import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890

open PEqualNP.CircuitLowerBounds

def edgeFunction (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def adjacent (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 3
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | _ => 4

def lowAssignment (v : Fin 10) (i : Fin 10) : Bool := decide (i = adjacent v)

def highAssignment (v : Fin 10) (i : Fin 10) : Bool :=
  decide (i = v ∨ i = adjacent v)

lemma assignments_agree {v i : Fin 10} (h : i ≠ v) :
    lowAssignment v i = highAssignment v i := by
  simp [lowAssignment, highAssignment, h]

lemma assignments_seed (v : Fin 10) :
    (lowAssignment v 0 && lowAssignment v 2) =
      (highAssignment v 0 && highAssignment v 2) := by
  revert v
  decide +kernel

lemma assignments_separate (v : Fin 10) :
    edgeFunction (lowAssignment v) ≠ edgeFunction (highAssignment v) := by
  revert v
  decide +kernel

lemma computes_surjective (C : Circuit) (σ : Fin 10 → Fin 10)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [x 0 && x 2]) = edgeFunction x) :
    Function.Surjective σ := by
  classical
  intro v
  by_contra missing
  have absent (i : Fin 10) : σ i ≠ v := fun h => missing ⟨i, h⟩
  have inputsEqual :
      List.ofFn (lowAssignment v ∘ σ) ++ [lowAssignment v 0 && lowAssignment v 2] =
      List.ofFn (highAssignment v ∘ σ) ++ [highAssignment v 0 && highAssignment v 2] := by
    have values : lowAssignment v ∘ σ = highAssignment v ∘ σ := by
      funext i
      exact assignments_agree (absent i)
    rw [values, assignments_seed]
  have outputsEqual := congrArg C.eval inputsEqual
  rw [computes (lowAssignment v), computes (highAssignment v)] at outputsEqual
  exact assignments_separate v outputsEqual

end PEqualNP.Outside.L_meta_1890
