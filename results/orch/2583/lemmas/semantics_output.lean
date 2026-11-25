import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.Output

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

lemma run_length (gs : List Gate) (xs : List Bool) :
    (run gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (xs ++ [_])).length = _
    rw [ih]
    simp
    omega

lemma run_input (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (run gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (xs ++ [_])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma output_input {n : ℕ} (C : Circuit) (h : C.output < n) (x : Fin n → Bool) :
    circuitFun n C x = x ⟨C.output, h⟩ := by
  change (run C.gates (List.ofFn x)).getD C.output false = _
  have hi : C.output < (List.ofFn x).length := by simpa using h
  rw [run_input _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

lemma output_missing {n : ℕ} (C : Circuit) (h : n + C.size ≤ C.output)
    (x : Fin n → Bool) : circuitFun n C x = false := by
  change (run C.gates (List.ofFn x)).getD C.output false = false
  apply List.getD_eq_default
  simpa only [run_length, List.length_ofFn, Circuit.size] using h

variable {N : ℕ} {C : Circuit} (I : Fin N → Fin N → Prop) [DecidableRel I]

lemma rejects_singletons
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (v : Fin (N + N)) :
    circuitFun (N + N) C (fun i => decide (i = v)) = false := by
  rw [hC, decide_eq_false_iff_not]
  rintro ⟨p, l, _, hp, hl⟩
  have hp' : Fin.castAdd N p = v := of_decide_eq_true hp
  have hl' : Fin.natAdd N l = v := of_decide_eq_true hl
  have he := congrArg Fin.val (hp'.trans hl'.symm)
  change p.val = N + l.val at he
  omega

lemma output_not_input
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    N + N ≤ C.output := by
  by_contra h
  have hi : C.output < N + N := by omega
  let v : Fin (N + N) := ⟨C.output, hi⟩
  have hv := rejects_singletons I hC v
  rw [output_input C hi] at hv
  simp [v] at hv

lemma output_valid
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (nonempty : ∃ p l, I p l) :
    C.output < N + N + C.size := by
  by_contra h
  have ht : circuitFun (N + N) C (fun _ => true) = true := by
    rw [hC, decide_eq_true_eq]
    obtain ⟨p, l, hpl⟩ := nonempty
    exact ⟨p, l, hpl, rfl, rfl⟩
  rw [output_missing C (by omega)] at ht
  contradiction

lemma output_gate
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true))
    (nonempty : ∃ p l, I p l) :
    ∃ j < C.size, C.output = N + N + j := by
  have hlo := output_not_input I hC
  have hhi := output_valid I hC nonempty
  exact ⟨C.output - (N + N), by omega, by omega⟩

lemma plane_output_gate (q : ℕ) (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (lines : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hC : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) :
    ∃ j < C.size, C.output = N + N + j := by
  apply output_gate I hC
  have hpos : 0 < N := by omega
  let l : Fin N := ⟨0, hpos⟩
  have hc : 0 < (Finset.univ.filter (fun p => I p l)).card := by rw [lines]; omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hc
  exact ⟨p, l, (Finset.mem_filter.mp hp).2⟩

end PEqualNP.Outside.L_meta_2583_aux.Output
