import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.CircuitBoundary

open PEqualNP.CircuitLowerBounds

lemma snoc_mono (a b : List Bool) (p q : Bool)
    (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true)
    (hpq : p = true → q = true) :
    ∀ i, (a ++ [p]).getD i false = true → (b ++ [q]).getD i false = true := by
  intro i hi
  by_cases hlt : i < a.length
  · rw [List.getD_append _ _ _ _ hlt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact hab i hi
  · by_cases heq : i = a.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, hlen] using hpq (by
        simpa [List.getD_eq_getElem?_getD] using hi)
    · have hfalse : (a ++ [p]).getD i false = false := by
        apply List.getD_eq_default
        simp only [List.length_append, List.length_singleton]
        omega
      exact Bool.noConfusion (hfalse.symm.trans hi)

lemma gate_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
    g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with h | h <;> rw [h]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro ha i hi
    exact hab i (ha i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ha⟩
    exact ⟨i, hi, hab i ha⟩

lemma fold_mono (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (a b : List Bool) (hlen : a.length = b.length)
    (hab : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (Circuit.wires ⟨gs, 0⟩ a).getD i false = true →
      (Circuit.wires ⟨gs, 0⟩ b).getD i false = true := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    have hg := legal g (by simp)
    have hs : ∀ h ∈ gs, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact legal h (by simp [hh])
    exact ih hs _ _ (by simp [hlen]) (snoc_mono a b _ _ hlen hab (gate_mono g hg a b hab))

lemma circuit_monotone (n : ℕ) (C : Circuit)
    (legal : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply fold_mono C.gates legal (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro i hi
  by_cases hlt : i < n
  · simpa [List.getD_eq_getElem, hlt] using hxy ⟨i, hlt⟩ (by
      simpa [List.getD_eq_getElem, hlt] using hi)
  · simp [Nat.le_of_not_gt hlt] at hi

end PEqualNP.Outside.L_meta_1031_aux.CircuitBoundary
