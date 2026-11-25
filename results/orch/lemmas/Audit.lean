import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2602_aux

open PEqualNP.CircuitLowerBounds

lemma derivative_unique (n : ℕ) (C : Circuit)
    (legal : ∀ j g, C.gates[j]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ a b, g.inputs = [a,b] ∧ a < n+j ∧ b < n+j)
    (v d e : ℕ → Bool)
    (initial : ∀ i < n, d i = e i)
    (rd : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = GateOp.and → d (n+j) = (v a && d b || d a && v b)) ∧
      (g.op = GateOp.or → d (n+j) = (d a || d b)))
    (re : ∀ j g a b, C.gates[j]? = some g → g.inputs = [a,b] →
      (g.op = GateOp.and → e (n+j) = (v a && e b || e a && v b)) ∧
      (g.op = GateOp.or → e (n+j) = (e a || e b))) :
    ∀ i < n+C.size, d i = e i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases low : i < n
    · exact initial i low
    · have hn : n ≤ i := Nat.le_of_not_gt low
      have hj : i-n < C.gates.length := by
        change i < n+C.gates.length at hi
        omega
      let g := C.gates[i-n]
      have hg : C.gates[i-n]? = some g := List.getElem?_eq_getElem hj
      obtain ⟨op,a,b,inputs,ha,hb⟩ := legal (i-n) g hg
      have eqi : n+(i-n) = i := by omega
      have aa : d a = e a := ih a (by omega) (by omega)
      have bb : d b = e b := ih b (by omega) (by omega)
      obtain ⟨da,dor⟩ := rd (i-n) g a b hg inputs
      obtain ⟨ea,eo⟩ := re (i-n) g a b hg inputs
      rcases op with hand | hor
      · rw [← eqi, da hand, ea hand, aa, bb]
      · rw [← eqi, dor hor, eo hor, aa, bb]

lemma audit_wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length+C.size := by
  let step := fun (w : List Bool) (g : Gate) =>
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have h (gs : List Gate) (w : List Bool) :
      (gs.foldl step w).length = w.length+gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih =>
      simp only [List.foldl_cons, ih, step, List.length_append,
        List.length_cons, List.length_nil]
      omega
  exact h C.gates x

lemma output_in_range (n : ℕ) (C : Circuit)
    (accepts : ∃ x : Fin n → Bool, C.eval (List.ofFn x) = true) :
    C.output < n+C.size := by
  obtain ⟨x,hx⟩ := accepts
  by_contra! outside
  change (C.wires (List.ofFn x)).getD C.output false = true at hx
  rw [List.getD_eq_default _ _ (by simpa [audit_wires_length] using outside)] at hx
  contradiction

end PEqualNP.Outside.L_meta_2602_aux
