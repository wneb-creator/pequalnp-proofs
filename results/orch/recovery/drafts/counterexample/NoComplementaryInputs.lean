import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof

open PEqualNP.CircuitLowerBounds

lemma drop_constant (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ)
    (hp : p < gs.length) (c : Bool)
    (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      nonNotCount gs' ≤ nonNotCount (gs.eraseIdx p) ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  rw [List.eraseIdx_append_of_length_le le_rfl, Nat.sub_self, List.eraseIdx_cons_zero]
  have count_append : nonNotCount (pre ++ post) = nonNotCount pre + nonNotCount post := by
    simp [nonNotCount]
  rw [count_append]
  apply drop_core k pre g post hcl o (Sum.inl c) ?_ hnc
  intro y
  refine ⟨by trivial, ?_⟩
  change c = vl (pre ++ g :: post) y (k + pre.length)
  exact (heq y).symm

end PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof

namespace PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof.Readers

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof

lemma Least.no_constant {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (least : Least m f gs o) (nonconstant : ∃ x y : Fin m → Bool, f x ≠ f y)
    (p : ℕ) (hp : p < gs.length) (c : Bool) :
    ¬ ∀ x : Fin m → Bool, vl gs x (m + p) = c := by
  intro constant
  obtain ⟨gs', o', clean, shorter, cost, computes⟩ :=
    drop_constant m gs least.hcl o p hp c constant (least.ncv nonconstant)
  have cost' : nonNotCount gs' ≤ nonNotCount gs :=
    cost.trans (List.eraseIdx_sublist gs p).countP_le
  have minimal := least.hmin gs' o' clean
    (fun x => by rw [computes x]; exact least.hev x) cost'
  omega

lemma Least.no_complementary_inputs {m : ℕ} {f : (Fin m → Bool) → Bool}
    {gs : List Gate} {o : ℕ} (least : Least m f gs o)
    (nonconstant : ∃ x y : Fin m → Bool, f x ≠ f y)
    {p : ℕ} {g : Gate} (atGate : gs[p]? = some g)
    (binary : g.op = GateOp.and ∨ g.op = GateOp.or) {a b : ℕ}
    (inputs : g.inputs = [a, b]) :
    ¬ ∀ x : Fin m → Bool, vl gs x b = !(vl gs x a) := by
  intro complements
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 atGate).1
  rcases binary with hand | hor
  · apply least.no_constant nonconstant p hp false
    intro x
    rw [vl_gate gs least.hcl x p g atGate, inputs, hand]
    cases ha : vl gs x a <;> simp [GateOp.eval, complements x, ha]
  · apply least.no_constant nonconstant p hp true
    intro x
    rw [vl_gate gs least.hcl x p g atGate, inputs, hor]
    cases ha : vl gs x a <;> simp [GateOp.eval, complements x, ha]

end PEqualNP.Outside.L_meta_2592.BinaryFloor.CircuitProof.Readers
