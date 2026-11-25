import ClosedOrSafety
import SoleReaderFactor
import StrongRelaxOrSafety

namespace PEqualNP.Outside.L_meta_1884.ClosedRelaxOr

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix

lemma prefix_value (n : Nat) (D : Circuit) (pre post : List Gate) (g : Gate)
    (hd : D.gates = pre ++ g :: post) (a : Nat) (ha : a < n + pre.length)
    (x : Fin n → Bool) :
    (D.wires (List.ofFn x)).getD a false = (SoleReader.run pre (List.ofFn x)).getD a false := by
  have hl : (pre.foldl Lift.step (List.ofFn x)).length = n + pre.length := by
    simp only [Lift.foldl_step_length, List.length_ofFn]
  have hstep : a < (Lift.step (pre.foldl Lift.step (List.ofFn x)) g).length := by
    simp only [Lift.step, List.length_append, List.length_singleton]
    omega
  rw [Lift.wires_eq, hd, List.foldl_append, List.foldl_cons]
  rw [Lift.foldl_step_getD post _ a hstep]
  rw [Lift.step, Lift.getD_append_left _ _ a (by omega)]
  rfl

theorem sole_or_impossible (D : Circuit) (pre post : List Gate) (t : Fin 9)
    (a : Nat) (T : Finset Nat) (ht : t = 2 ∨ t = 8)
    (hd : D.gates = pre ++ ⟨GateOp.or, [t.val, a]⟩ :: post)
    (hat : a ≠ t.val)
    (hpre : ∀ g ∈ pre, t.val ∉ g.inputs)
    (hpost : ∀ g ∈ post, t.val ∉ g.inputs)
    (hout : D.output ≠ t.val)
    (hM : Monotone2 D) (hR : ReadsBack 9 D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun 9 E = circuitFun 9 D → D.size ≤ E.size)
    (hA : PA D T) (hB : PB 9 D T) (hC : PC 9 D T)
    (hcofactor : ∀ x : Fin 9 → Bool, x t = false →
      circuitFun 9 D x = StrongRelaxOrSafety.target x)
    (hpositive : ∀ x, StrongRelaxOrSafety.target x = true → circuitFun 9 D x = true)
    (hexceptional : circuitFun 9 D StrongRelaxOrSafety.exceptional = true)
    (hsingle : circuitFun 9 D (fun i => decide (i = t)) = false) : False := by
  have hg : D.gates[pre.length]? = some ⟨GateOp.or, [t.val, a]⟩ := by simp [hd]
  have ha : a < 9 + pre.length := readsBack_get 9 D hR _ _ hg a (by simp)
  have hpfx := prefix_value 9 D pre post _ hd a ha
  have hDeq : D = ⟨pre ++ ⟨GateOp.or, [t.val, a]⟩ :: post, D.output⟩ := by
    cases D
    simp_all
  have hsafe : ∀ x : Fin 9 → Bool,
      (D.wires (List.ofFn x)).getD a false = true → StrongRelaxOrSafety.target x = true := by
    apply StrongRelaxOrSafety.partner_safe t ht (circuitFun 9 D)
      (fun x => (D.wires (List.ofFn x)).getD a false)
      hcofactor hpositive hexceptional
    · exact ClosedOrSafety.wire_mono 9 D hM a
    · intro x y off
      rw [hpfx x, hpfx y]
      exact SoleReader.partner_independent pre _ _ (SoleReader.ofFn_agree t x y off) hpre hat
    · intro x y off same
      rw [hpfx x, hpfx y] at same
      have hf := SoleReader.factor_or pre post t a D.output x y off hpre hpost hout same
      simpa only [← hDeq, circuitFun] using hf
  apply ClosedOrSafety.excludes_or_pair 9 D T hM hR hmin hA hB hC
    pre.length a t.val hg (fun x hx => hpositive x (hsafe x hx))
    (fun i => decide (i = t)) _ hsingle
  rw [LowMergeProof.wires_input D _ t.val (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left t.isLt,
    Option.getD_some]
  simp

end PEqualNP.Outside.L_meta_1884.ClosedRelaxOr
