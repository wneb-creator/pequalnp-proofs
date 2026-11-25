import ClosedOrSafety
import StrongRelaxRows
import PEqualNP.MetaComplexity.Helpers.LiveSize
import PEqualNP.MetaComplexity.Helpers.NormalFormLift

namespace PEqualNP.Outside.L_meta_1884.LeastGateFacts

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix

lemma live (n : Nat) (D : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n D → D.size ≤ E.size)
    (k : Nat) (hk : k < D.gates.length) (hout : D.output ≠ n + k) :
    ∃ (j : Nat) (g : Gate), D.gates[j]? = some g ∧ n + k ∈ g.inputs := by
  by_contra hnone
  have hun : ∀ j < D.gates.length, n + k ∉ (gateAt D j).inputs := by
    intro j hj hin
    exact hnone ⟨j, gateAt D j, gateAt_some D j hj, hin⟩
  have hAO' := LiveSize.delU_AO n k D hAO hk
  have hfun := LiveSize.delU_fun n k D hAO hk hun hout
  have hsize := hmin (LiveSize.delU n k D) (mono_of_AO2 n _ hAO') hfun
  have hlen := LiveSize.delU_length n k D hk
  simp only [Circuit.size] at hsize
  omega

lemma post_reader (n : Nat) (D : Circuit) (pre post : List Gate) (g : Gate)
    (hd : D.gates = pre ++ g :: post) (hAO : PEqualNP.TopForm.IsAO2 n D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n D → D.size ≤ E.size)
    (hout : D.output ≠ n + pre.length) :
    ∃ r ∈ post, n + pre.length ∈ r.inputs := by
  have hk : pre.length < D.gates.length := by simp [hd]
  obtain ⟨j, r, hr, hin⟩ := live n D hAO hmin pre.length hk hout
  have hlt := readsBack_get n D hAO.2.1 j r hr (n + pre.length) hin
  have hd' : D.gates.drop (pre.length + 1) = post := by simp [hd]
  have hget : post[j - (pre.length + 1)]? = some r := by
    rw [← hd', List.getElem?_drop]
    convert hr using 1 <;> congr 1 <;> omega
  exact ⟨r, List.mem_of_getElem? hget, hin⟩

lemma output_not_and_reader (D : Circuit) (hR : ReadsBack 9 D)
    (k : Nat) (g : Gate) (hg : D.gates[k]? = some g) (hop : g.op = GateOp.and)
    (hin : 2 ∈ g.inputs)
    (hcorrect : ∀ x : Fin 9 → Bool, x 2 = false → circuitFun 9 D x = StrongRelaxRows.target x) :
    D.output ≠ 9 + k := by
  intro hout
  have hpos : circuitFun 9 D (StrongRelaxRows.row 3) = true := by
    rw [hcorrect _ (by decide)]
    decide
  change (D.wires (List.ofFn (StrongRelaxRows.row 3))).getD D.output false = true at hpos
  rw [hout, ClosedOrSafety.gate_value 9 D hR k g hg _] at hpos
  simp only [hop, GateOp.eval, List.all_eq_true] at hpos
  have hbad := hpos _ (List.mem_map.mpr ⟨2, hin, rfl⟩)
  simp only [id] at hbad
  rw [LowMergeProof.wires_input D _ 2 (by simp)] at hbad
  change false = true at hbad
  cases hbad

end PEqualNP.Outside.L_meta_1884.LeastGateFacts
