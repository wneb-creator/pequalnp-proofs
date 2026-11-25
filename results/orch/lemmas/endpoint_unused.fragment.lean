namespace PEqualNP.Outside.L_meta_1886_aux.EndpointOrder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep
open MapRigidity

lemma away_last (w : List Bool) (a b : Bool) : awayLE w.length (w ++ [a]) (w ++ [b]) := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hlt]
  · have hwa : (w ++ [a]).length ≤ i := by simp; omega
    have hwb : (w ++ [b]).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hwa,List.getD_eq_default _ _ hwb]

lemma unused_last_output (gs : List Gate) (w : List Bool) (outIdx : Nat) (a b : Bool)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (unused : ∀ g ∈ gs, w.length ∉ g.inputs) (out : outIdx ≠ w.length) :
    (run gs (w ++ [a])).getD outIdx false = (run gs (w ++ [b])).getD outIdx false := by
  apply le_antisymm
  · exact run_away w.length gs mono unused (by simp) (away_last w a b) outIdx out
  · exact run_away w.length gs mono unused (by simp) (away_last w b a) outIdx out

lemma unused_not_replace (p : Fin 10) (pre suffix : List Gate) (outIdx : Nat) (rest : List Nat)
    (monoSuffix : ∀ g ∈ suffix, g.op = .and ∨ g.op = .or)
    (unused : ∀ g ∈ suffix, 11 + pre.length ∉ g.inputs)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,p.val :: rest⟩ :: suffix) outIdx).eval (initial x) = edge10 x)
    (b : Bool) : ∀ x : Fin 10 → Bool,
      (Circuit.mk suffix outIdx).eval (run pre (initial x) ++ [b]) = edge10 x := by
  have outputDifferent : outIdx ≠ 11 + pre.length := by
    intro eq
    let xzero : Fin 10 → Bool := fun _ => false
    let w := run pre (initial xzero)
    have len : w.length = 11 + pre.length := by simp [w,run_length,initial_length]
    have zeroPins : ∀ q : Fin 10, (initial xzero).getD q.val false = false := by decide +kernel
    have sourceZero : w.getD p.val false = false := by
      rw [show w = run pre (initial xzero) from rfl,
        run_prefix _ _ _ (by rw [initial_length]; omega)]
      exact zeroPins p
    have notStep : step w ⟨.not,p.val :: rest⟩ = w ++ [true] := by
      change w ++ [!(w.getD p.val false)] = w ++ [true]
      simp only [sourceZero,Bool.not_false]
    have h := computes xzero
    change (run (pre ++ ⟨.not,p.val :: rest⟩ :: suffix) (initial xzero)).getD outIdx false = _ at h
    rw [run_append] at h
    change (run suffix (step w ⟨.not,p.val :: rest⟩)).getD outIdx false = _ at h
    rw [notStep,eq,run_prefix _ _ _ (by simp; omega),←len,getD_last] at h
    have targetZero : edge10 xzero = false := rfl
    rw [targetZero] at h
    cases h
  intro x
  let w := run pre (initial x)
  have len : w.length = 11 + pre.length := by simp [w,run_length,initial_length]
  have same := unused_last_output suffix w outIdx b (!(w.getD p.val false)) monoSuffix
    (fun g hg => by rw [len]; exact unused g hg) (by rw [len]; exact outputDifferent)
  have h := computes x
  change (run (pre ++ ⟨.not,p.val :: rest⟩ :: suffix) (initial x)).getD outIdx false = _ at h
  rw [run_append] at h
  change (run suffix (w ++ [!(w.getD p.val false)])).getD outIdx false = _ at h
  change (run suffix (w ++ [b])).getD outIdx false = _
  exact same.trans h

end PEqualNP.Outside.L_meta_1886_aux.EndpointOrder
