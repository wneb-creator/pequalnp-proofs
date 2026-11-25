import PEqualNP.Outside.L_meta_5236
import CutFloor

namespace PEqualNP.Outside.L_meta_2592_aux.DeletionFifteen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof
open PEqualNP.Outside.L_meta_2592_aux.Restriction
open PEqualNP.Outside.L_meta_2592_aux.CutFloor

lemma deletion_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 9 → Bool,
      C.eval (List.ofFn x) = PEqualNP.Outside.L_meta_5236.edge x) :
    15 ≤ nonNotCount C.gates := by
  by_contra! small
  have countEq : C.gates.countP (fun g => !PEqualNP.Outside.L_meta_5236.isNot g) =
      nonNotCount C.gates := by
    unfold nonNotCount
    congr 1
    funext g
    cases g.op <;> rfl
  obtain ⟨k, S, bound, run, raw⟩ := PEqualNP.Outside.L_meta_5236.raw_signed C fan
    (by rw [countEq]; omega) correct
  rw [PEqualNP.Outside.L_meta_5236.orbitAllInputs run raw] at run
  exact PEqualNP.Outside.L_meta_5236.rootSImpossible k bound run

lemma cut_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (v : Fin 10) :
    15 + cutCost (initialOrigins 10) v.val C.gates ≤ nonNotCount C.gates := by
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
  have floor : 15 ≤ nonNotCount D.gates := by
    apply deletion_floor D fanD
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
    simp [petersen, PEqualNP.Outside.L_meta_5236.edge]
  omega

end PEqualNP.Outside.L_meta_2592_aux.DeletionFifteen
