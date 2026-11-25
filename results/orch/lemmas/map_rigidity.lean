import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1886_aux.MapRigidity

open PEqualNP.CircuitLowerBounds

def edge10 (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def bonus (choice : Bool) (x : Fin 10 → Bool) : Bool :=
  if choice = true then x 0 && x 1 else x 0 || x 1

def neighbor (choice : Bool) (i : Fin 10) : Fin 10 :=
  if i = 0 then if choice then 5 else 1
  else if i = 1 then if choice then 2 else 0
  else ![1,0,1,2,0,0,1,2,3,4] i

def low (choice : Bool) (i : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = neighbor choice i)

def high (choice : Bool) (i : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = i ∨ j = neighbor choice i)

lemma witness_checked : ∀ (choice : Bool) (i : Fin 10),
    bonus choice (low choice i) = bonus choice (high choice i) ∧
      edge10 (low choice i) ≠ edge10 (high choice i) := by
  decide +kernel

lemma collision (choice : Bool) (i : Fin 10) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ bonus choice x = bonus choice y ∧ edge10 x ≠ edge10 y := by
  refine ⟨low choice i,high choice i,?_,witness_checked choice i⟩
  intro j hj
  simp [low,high,hj]

lemma input_map_surjective (C : Circuit) (p : Fin 10 → Fin 10) (choice : Bool)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [bonus choice x]) = edge10 x) :
    Function.Surjective p := by
  intro i
  by_contra missing
  have absent : ∀ j, p j ≠ i := by
    intro j h
    exact missing ⟨j,h⟩
  obtain ⟨x,y,equal,bonusEqual,outputsDiffer⟩ := collision choice i
  have pinsEqual : x ∘ p = y ∘ p := funext (fun j => equal (p j) (absent j))
  have inputEqual : List.ofFn (x ∘ p) ++ [bonus choice x] =
      List.ofFn (y ∘ p) ++ [bonus choice y] := by rw [pinsEqual,bonusEqual]
  have outputEqual := congrArg C.eval inputEqual
  rw [computes x,computes y] at outputEqual
  exact outputsDiffer outputEqual

lemma input_map_bijective (C : Circuit) (p : Fin 10 → Fin 10) (choice : Bool)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [bonus choice x]) = edge10 x) :
    Function.Bijective p := by
  exact Finite.surjective_iff_bijective.mp (input_map_surjective C p choice computes)

end PEqualNP.Outside.L_meta_1886_aux.MapRigidity
