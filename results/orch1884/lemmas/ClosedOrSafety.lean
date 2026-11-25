import ClosedOrSet

namespace PEqualNP.Outside.L_meta_1884.ClosedOrSafety

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.LiftFix

lemma gate_value (n : Nat) (D : Circuit) (hR : ReadsBack n D)
    (k : Nat) (g : Gate) (hg : D.gates[k]? = some g) (x : Fin n → Bool) :
    (D.wires (List.ofFn x)).getD (n + k) false =
      g.op.eval (g.inputs.map fun i => (D.wires (List.ofFn x)).getD i false) := by
  have hk := (List.getElem?_eq_some_iff.mp hg).1
  have hkg := (List.getElem?_eq_some_iff.mp hg).2
  have he := LowMergeProof.wires_gate D (List.ofFn x) k hk
  simp only [List.length_ofFn, hkg] at he
  rw [he]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact ite_eq_left (readsBack_get n D hR k g hg i hi)

theorem excludes_or_pair (n : Nat) (D : Circuit) (T : Finset Nat)
    (hM : Monotone2 D) (hR : ReadsBack n D)
    (hmin : ∀ E : Circuit, Monotone2 E → circuitFun n E = circuitFun n D → D.size ≤ E.size)
    (hA : PA D T) (hB : PB n D T) (hC : PC n D T)
    (k a t : Nat) (hg : D.gates[k]? = some ⟨GateOp.or, [t, a]⟩)
    (hsafe : ∀ x : Fin n → Bool,
      (D.wires (List.ofFn x)).getD a false = true → circuitFun n D x = true)
    (x : Fin n → Bool) (hxt : (D.wires (List.ofFn x)).getD t false = true)
    (hxout : circuitFun n D x = false) : False := by
  by_cases hsat : ∃ y : Fin n → Bool, (D.wires (List.ofFn y)).getD a false = true
  · exact ClosedOrSet.excludes_safe_or n D T hR hA hB hC k _ hg rfl
      a t (by simp) (by simp) hsat hsafe x hxt hxout
  · have haf : ∀ y : Fin n → Bool, (D.wires (List.ofFn y)).getD a false = false := by
      intro y
      cases he : (D.wires (List.ofFn y)).getD a false
      · rfl
      · exact False.elim (hsat ⟨y, he⟩)
    apply ClosedOrSet.no_copy n D hM hR hmin k t
      (List.getElem?_eq_some_iff.mp hg).1
      (readsBack_get n D hR k _ hg t (by simp))
    intro y
    rw [gate_value n D hR k _ hg y]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      Bool.or_false, id, haf y]

lemma wire_mono (n : Nat) (D : Circuit) (hM : Monotone2 D)
    (i : Nat) (x y : Fin n → Bool) (hle : ∀ j, x j = true → y j = true) :
    (D.wires (List.ofFn x)).getD i false = true →
      (D.wires (List.ofFn y)).getD i false = true := by
  apply LowMergeProof.wires_mono D (fun g hg => by simpa using (hM g hg).1)
    (List.ofFn x) (List.ofFn y) (by simp)
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = true := by
      simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hjn,
        Option.getD_some] using hj
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, dite_eq_left hjn,
      Option.getD_some] using hle ⟨j, hjn⟩ hx
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hj
    cases hj

lemma output_mono (n : Nat) (D : Circuit) (hM : Monotone2 D)
    (x y : Fin n → Bool) (hle : ∀ j, x j = true → y j = true) :
    circuitFun n D x = true → circuitFun n D y = true :=
  wire_mono n D hM D.output x y hle

end PEqualNP.Outside.L_meta_1884.ClosedOrSafety
