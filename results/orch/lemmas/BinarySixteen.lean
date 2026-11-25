import CutFloor
import FirstBinary
import Compression

namespace PEqualNP.Outside.L_meta_2592_aux.BinarySixteen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7493.CircuitProof
open PEqualNP.Outside.L_meta_7493.CircuitProof.Readers
open PEqualNP.Outside.L_meta_2592_aux.Restriction

lemma petersen_nonconstant : ∃ x y : Fin 10 → Bool, petersen x ≠ petersen y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩

lemma petersen_not_unary (v : Fin 10) (sign : Bool) :
    ¬ ∀ x : Fin 10 → Bool, petersen x = if sign then !(x v) else x v := by
  intro unary
  have low := unary (Function.update (fun _ => false) v false)
  have high := unary (Function.update (fun _ => true) v false)
  rw [(FirstOrigin.petersen_cofactor_values v false).1] at low
  rw [(FirstOrigin.petersen_cofactor_values v false).2] at high
  simp only [Function.update_self] at low high
  cases sign with
  | false => simpa using high
  | true => simpa using low

lemma cutCost_eq (origins : List (Option ℕ)) (v : ℕ) (gs : List Gate) :
    FirstMerge.cutCost origins v gs =
      PEqualNP.Outside.L_meta_2592_restrict.CircuitProof.cutCost origins v gs := by
  induction gs generalizing origins with
  | nil => rfl
  | cons g gs ih =>
    simp only [FirstMerge.cutCost,
      PEqualNP.Outside.L_meta_2592_restrict.CircuitProof.cutCost, ih]
    rfl

theorem binary_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    16 ≤ nonNotCount C.gates := by
  by_contra! small
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C fan correct petersen_nonconstant
  let D : Circuit := ⟨gs, o⟩
  have fanD : FanInTwo D := fun g hg => (clean_nok 10 gs least.hcl g hg).1
  have correctD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := least.hev
  have bound : nonNotCount D.gates ≤ 15 := by
    change nonNotCount gs ≤ 15
    omega
  have costs (v : Fin 10) :
      FirstMerge.cutCost (List.ofFn (fun i : Fin 10 => some i.val)) v.val D.gates ≤ 1 :=
    by
      rw [cutCost_eq]
      exact CutFloor.cut_at_most_one D fanD correctD bound v
  obtain ⟨pre, g, post, u, v, code, split, allNot, op, distinct,
    readU, readV, factor⟩ :=
    FirstBinary.least_first_binary least petersen_nonconstant petersen_not_unary
  have flag : FirstMerge.isNotGate g.op = false := by
    rcases op with op | op <;> simp [FirstMerge.isNotGate, op]
  exact Compression.no_first_compression D pre post g split allNot flag u v distinct
    code factor readU readV (costs u) (costs v) correctD

end PEqualNP.Outside.L_meta_2592_aux.BinarySixteen
