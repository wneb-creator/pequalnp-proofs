import DeletionFifteen
import BinarySixteen

namespace PEqualNP.Outside.L_meta_2592_aux.BinarySeventeen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_7493.CircuitProof
open PEqualNP.Outside.L_meta_7493.CircuitProof.Readers
open PEqualNP.Outside.L_meta_2592_aux.Restriction
open PEqualNP.Outside.L_meta_2592_aux.BinarySixteen

theorem binary_floor (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    17 ≤ nonNotCount C.gates := by
  by_contra! small
  obtain ⟨gs, o, least, budget⟩ := least_with_budget C fan correct petersen_nonconstant
  let D : Circuit := ⟨gs, o⟩
  have fanD : FanInTwo D := fun g hg => (clean_nok 10 gs least.hcl g hg).1
  have correctD : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := least.hev
  have costs (v : Fin 10) :
      FirstMerge.cutCost (List.ofFn (fun i : Fin 10 => some i.val)) v.val D.gates ≤ 1 := by
    rw [cutCost_eq]
    change PEqualNP.Outside.L_meta_2592_restrict.CircuitProof.cutCost
      (PEqualNP.Outside.L_meta_2592_restrict.CircuitProof.initialOrigins 10) v.val D.gates ≤ 1
    have floor := DeletionFifteen.cut_floor D fanD correctD v
    change 15 + _ ≤ nonNotCount gs at floor
    omega
  obtain ⟨pre, g, post, u, v, code, split, allNot, op, distinct,
    readU, readV, factor⟩ :=
    FirstBinary.least_first_binary least petersen_nonconstant petersen_not_unary
  have flag : FirstMerge.isNotGate g.op = false := by
    rcases op with op | op <;> simp [FirstMerge.isNotGate, op]
  exact Compression.no_first_compression D pre post g split allNot flag u v distinct
    code factor readU readV (costs u) (costs v) correctD

end PEqualNP.Outside.L_meta_2592_aux.BinarySeventeen
