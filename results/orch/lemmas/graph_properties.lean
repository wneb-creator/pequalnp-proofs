import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ptEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

def ptFun (x : Fin 10 → Bool) : Bool :=
  ptEdges.any fun e => x e.1 && x e.2

lemma ptFun_eq (x : Fin 10 → Bool) :
    ptFun x = (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 ||
      x 4 && x 0 || x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
      x 4 && x 9 || x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 ||
      x 8 && x 5) := by
  simp [ptFun, ptEdges, Bool.or_assoc]

lemma ptFun_monotone : Monotone ptFun := by
  intro x y hxy
  apply Bool.le_iff_imp.mpr
  intro hx
  obtain ⟨e, he, hval⟩ := List.any_eq_true.mp hx
  apply List.any_eq_true.mpr
  refine ⟨e, he, ?_⟩
  have hs : x e.1 = true ∧ x e.2 = true := by simpa using hval
  simp only [Bool.and_eq_true]
  exact ⟨(Bool.le_iff_imp.mp (hxy e.1)) hs.1,
    (Bool.le_iff_imp.mp (hxy e.2)) hs.2⟩

set_option maxRecDepth 2000 in
set_option maxHeartbeats 400000 in
lemma ptFun_essential : ∀ i : Fin 10, ∃ x : Fin 10 → Bool,
    ptFun (Function.update x i false) ≠ ptFun (Function.update x i true) := by
  let neighbor : Fin 10 → Fin 10 := ![1, 0, 1, 2, 0, 0, 1, 2, 3, 4]
  have cert : ∀ i : Fin 10,
      ptFun (Function.update (fun j => decide (j = neighbor i)) i false) = false ∧
      ptFun (Function.update (fun j => decide (j = neighbor i)) i true) = true := by
    decide
  intro i
  refine ⟨fun j => decide (j = neighbor i), ?_⟩
  rw [(cert i).1, (cert i).2]
  decide

end PEqualNP.Outside.L_meta_2592
