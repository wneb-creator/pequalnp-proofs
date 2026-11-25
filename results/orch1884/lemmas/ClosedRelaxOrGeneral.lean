import ClosedRelaxOr

namespace PEqualNP.Outside.L_meta_1884.ClosedRelaxOrGeneral

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix

lemma excludes_or (n : Nat) (D : Circuit) (T : Finset Nat)
    (hM : Monotone2 D) (hR : ReadsBack n D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n D → D.size ≤ E.size)
    (hA : PA D T) (hB : PB n D T) (hC : PC n D T)
    (k a t : Nat) (g : Gate) (hg : D.gates[k]? = some g) (hop : g.op = GateOp.or)
    (hin : g.inputs = [t, a] ∨ g.inputs = [a, t])
    (hsafe : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).getD a false = true → circuitFun n D x = true)
    (x : Fin n → Bool) (hxt : (D.wires (List.ofFn x)).getD t false = true)
    (hxout : circuitFun n D x = false) : False := by
  have hain : a ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have htin : t ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  by_cases hsat : ∃ y : Fin n → Bool, (D.wires (List.ofFn y)).getD a false = true
  · exact ClosedOrSet.excludes_safe_or n D T hR hA hB hC k g hg hop
      a t hain htin hsat hsafe x hxt hxout
  · have haf : ∀ y : Fin n → Bool, (D.wires (List.ofFn y)).getD a false = false := by
      intro y
      cases he : (D.wires (List.ofFn y)).getD a false
      · rfl
      · exact False.elim (hsat ⟨y, he⟩)
    apply ClosedOrSet.no_copy n D hM hR hmin k t (List.getElem?_eq_some_iff.mp hg).1
      (readsBack_get n D hR k g hg t htin)
    intro y
    rw [ClosedOrSafety.gate_value n D hR k g hg y]
    rcases hin with hin | hin <;>
      simp only [hop, hin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
        List.any_nil, Bool.or_false, id, haf y, Bool.false_or]

theorem sole_or_impossible (D : Circuit) (pre post : List Gate) (t : Fin 9)
    (a : Nat) (g : Gate) (T : Finset Nat) (ht : t = 2 ∨ t = 8)
    (hd : D.gates = pre ++ g :: post) (hop : g.op = GateOp.or)
    (hin : g.inputs = [t.val, a] ∨ g.inputs = [a, t.val]) (hat : a ≠ t.val)
    (hpre : ∀ g ∈ pre, t.val ∉ g.inputs)
    (hpost : ∀ g ∈ post, t.val ∉ g.inputs) (hout : D.output ≠ t.val)
    (hM : Monotone2 D) (hR : ReadsBack 9 D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun 9 E = circuitFun 9 D → D.size ≤ E.size)
    (hA : PA D T) (hB : PB 9 D T) (hC : PC 9 D T)
    (hcofactor : ∀ x : Fin 9 → Bool, x t = false →
      circuitFun 9 D x = StrongRelaxOrSafety.target x)
    (hpositive : ∀ x, StrongRelaxOrSafety.target x = true → circuitFun 9 D x = true)
    (hexceptional : circuitFun 9 D StrongRelaxOrSafety.exceptional = true)
    (hsingle : circuitFun 9 D (fun i => decide (i = t)) = false) : False := by
  have hg : D.gates[pre.length]? = some g := by simp [hd]
  have hain : a ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have ha := readsBack_get 9 D hR _ _ hg a hain
  have hpfx := ClosedRelaxOr.prefix_value 9 D pre post g hd a ha
  have hDeq : D = ⟨pre ++ g :: post, D.output⟩ := by cases D; simp_all
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
      have hgate : g.op.eval (g.inputs.map fun i => (SoleReader.run pre (List.ofFn x)).getD i false) =
          g.op.eval (g.inputs.map fun i => (SoleReader.run pre (List.ofFn y)).getD i false) := by
        have hinput : ∀ z : Fin 9 → Bool,
            (SoleReader.run pre (List.ofFn z)).getD t.val false = z t := by
          intro z
          rw [SoleReader.run_input pre _ _ (by simp)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left t.isLt,
            Option.getD_some]
        rcases hin with hin | hin <;>
          simpa only [hop, hin, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, Bool.or_false, Bool.false_or, id, hinput, Bool.or_comm] using same
      have hf := SoleReader.factor pre post g _ _ (SoleReader.ofFn_agree t x y off)
        hpre hpost hout hgate
      simpa only [← hDeq, circuitFun] using hf
  apply excludes_or 9 D T hM hR hmin hA hB hC pre.length a t.val g hg hop hin
    (fun x hx => hpositive x (hsafe x hx)) (fun i => decide (i = t)) _ hsingle
  rw [LowMergeProof.wires_input D _ t.val (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left t.isLt,
    Option.getD_some]
  simp

end PEqualNP.Outside.L_meta_1884.ClosedRelaxOrGeneral
