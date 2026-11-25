import DirectFilterCore
import SharedFilterSafety

namespace PEqualNP.Outside.L_meta_1884.DirectFilterStructure

open PEqualNP.CircuitLowerBounds SharedFilter

def soleAfter (pre post : List Gate) (v : Fin 10) : Prop :=
  ∃ mid tail : List Gate,
    post = mid ++ ⟨GateOp.and,[v.val,11 + pre.length]⟩ :: tail ∧
      ∀ g ∈ mid ++ tail, v.val ∉ g.inputs

theorem facts (pre post : List Gate) (ins : List Nat) (o : Nat) (v : Fin 10)
    (hv : v ≠ 0) (allowed : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (away : ∀ g ∈ pre, v.val ∉ g.inputs) (hi : v.val ∉ ins) (ho : o ≠ v.val)
    (hsole : soleAfter pre post v)
    (hcompute : ∀ x : Fin 10 → Bool,
      Circuit.eval ⟨pre ++ ⟨.not,ins⟩ :: post,o⟩ (DirectFilter.seed x) =
        SoleOrPartner.target x) :
    fiberMono (DirectFilter.operand pre ins) ∧ independent v (DirectFilter.operand pre ins) ∧
      factor v (DirectFilter.operand pre ins) := by
  refine ⟨DirectFilter.operand_fiber_mono pre ins allowed,
    DirectFilter.operand_independent pre ins v hv away hi,?_⟩
  obtain ⟨mid,tail,hpost,hrest⟩ := hsole
  apply DirectFilter.factor pre mid tail ins v hv o SoleOrPartner.target away hi
    (fun g hg => hrest g (List.mem_append.mpr (Or.inl hg)))
    (fun g hg => hrest g (List.mem_append.mpr (Or.inr hg))) ho
  intro x
  simpa only [hpost,List.append_assoc,List.cons_append] using hcompute x

end PEqualNP.Outside.L_meta_1884.DirectFilterStructure
