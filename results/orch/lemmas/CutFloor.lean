import PEqualNP.Outside.L_meta_7493
import Restriction
import PairCode

namespace PEqualNP.Outside.L_meta_2592_aux.CutFloor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof
open PEqualNP.Outside.L_meta_2592_aux.Restriction

def restrictionSeed (v i : Fin 10) : Stat :=
  Fin.lastCases (Sum.inl false) (fun j : Fin 9 => Sum.inr j.val) (permInv v i)

lemma restrictionSeed_valid (v i : Fin 10) : (restrictionSeed v i).Valid 9 := by
  unfold restrictionSeed
  generalize permInv v i = j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · trivial
  · simpa only [Fin.lastCases_castSucc, Stat.Valid] using k.isLt

lemma restrictionSeed_eval (v : Fin 10) (x : Fin 9 → Bool) (i : Fin 10) :
    (restrictionSeed v i).val (List.ofFn x) = liftInput v x i := by
  unfold restrictionSeed liftInput
  generalize permInv v i = j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · rfl
  · simp only [Fin.lastCases_castSucc, Stat.val,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, k.isLt,
      dite_true, Option.getD_some]

lemma restrictionSeed_fixed (v : Fin 10) : restrictionSeed v v = Sum.inl false := by
  have eq : permInv v v = 9 := by
    have h := perm_inverse v 9
    rwa [perm_last] at h
  unfold restrictionSeed
  rw [eq]
  rfl

set_option maxHeartbeats 2000000 in
lemma cut_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (v : Fin 10) :
    14 + cutCost (initialOrigins 10) v.val C.gates ≤ nonNotCount C.gates := by
  have nonconstant : ∃ x y : Fin 9 → Bool,
      C.eval (List.ofFn (liftInput v x)) ≠ C.eval (List.ofFn (liftInput v y)) := by
    refine ⟨fun _ => false, fun _ => true, ?_⟩
    rw [correct, correct, liftInput_petersen, liftInput_petersen]
    decide
  obtain ⟨D, fanD, budget, computes⟩ := restriction_with_cutCost 9 10 C fan
    (List.ofFn (restrictionSeed v)) (initialOrigins 10) v.val (liftInput v)
    (inv_seed 9 10 (restrictionSeed v) (liftInput v)
      (restrictionSeed_valid v) (restrictionSeed_eval v))
    (originConstant_seed 10 (restrictionSeed v) v false (restrictionSeed_fixed v))
    nonconstant
  have floor : 14 ≤ nonNotCount D.gates := by
    apply PEqualNP.Outside.L_meta_7493.binaryFloor D fanD
    intro x
    rw [computes, correct, liftInput_petersen]
    have values : Fin.lastCases false x =
        ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, false] := by
      funext i
      refine Fin.lastCases ?_ (fun k => ?_) i
      · rfl
      · rw [Fin.lastCases_castSucc]
        fin_cases k <;> rfl
    rw [values]
    simp [petersen, PEqualNP.Outside.L_meta_7493.petersenF,
      PEqualNP.Outside.L_meta_7493.PetersenNine.edgeFun,
      PEqualNP.Outside.L_meta_7493.PetersenNine.edges]
    ac_rfl
  omega

lemma cut_at_most_one (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (budget : nonNotCount C.gates ≤ 15) (v : Fin 10) :
    cutCost (initialOrigins 10) v.val C.gates ≤ 1 := by
  have floor := cut_floor C fan correct v
  omega

end PEqualNP.Outside.L_meta_2592_aux.CutFloor
