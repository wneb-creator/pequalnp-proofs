import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.CircuitMoves

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_gateStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl gateStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih, gateStep, List.length_append, List.length_singleton]
    omega

lemma list_getD_append_left {α : Type} (l1 l2 : List α) (i : ℕ) (d : α)
    (hi : i < l1.length) : (l1 ++ l2).getD i d = l1.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left hi]

lemma foldl_gateStep_getD_of_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) : (gs.foldl gateStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : i < (gateStep w g).length := by
      simp only [gateStep, List.length_append, List.length_singleton]
      omega
    rw [ih (gateStep w g) hlen]
    exact list_getD_append_left w _ i false hi

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_gateStep_length C.gates x

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (C.wires (List.ofFn x)).getD i false = x ⟨i, hi⟩ := by
  rw [show (C.wires (List.ofFn x)).getD i false = (List.ofFn x).getD i false from
    foldl_gateStep_getD_of_lt C.gates (List.ofFn x) i (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi]

lemma incidence_singleton_false (P L : ℕ) (I : Fin P → Fin L → Prop)
    [DecidableRel I] (w : Fin (P + L)) :
    decide (∃ p l, I p l ∧ decide (Fin.castAdd L p = w) = true ∧
      decide (Fin.natAdd P l = w) = true) = false := by
  apply decide_eq_false
  rintro ⟨p, l, _, hp, hl⟩
  have hp' := of_decide_eq_true hp
  have hl' := of_decide_eq_true hl
  have he := congrArg Fin.val (hp'.trans hl'.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  omega

lemma no_input_below (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (w : ℕ) (hw : w < P + L) : ¬ WireBelowOutput (P + L) C w := by
  intro h
  let z : Fin (P + L) → Bool := fun i => decide (i = ⟨w, hw⟩)
  have hv : (C.wires (List.ofFn z)).getD w false = true := by
    rw [wires_input C z w hw]
    simp [z]
  have hc : circuitFun (P + L) C z = true := h z hv
  have hz : circuitFun (P + L) C z = false := by
    rw [hF]
    exact incidence_singleton_false P L I ⟨w, hw⟩
  rw [hz] at hc
  contradiction

lemma incidence_output_valid (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit) (hne : ∃ p l, I p l)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    C.output < P + L + C.gates.length := by
  by_contra hout
  have hzero : circuitFun (P + L) C (fun _ => true) = false := by
    unfold circuitFun Circuit.eval
    apply List.getD_eq_default
    rw [wires_length, List.length_ofFn]
    omega
  have hone : circuitFun (P + L) C (fun _ => true) = true := by
    rw [hF]
    apply decide_eq_true
    obtain ⟨p, l, hpl⟩ := hne
    exact ⟨p, l, hpl, rfl, rfl⟩
  rw [hzero] at hone
  contradiction

lemma incidence_output_is_gate (P L : ℕ) (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hF : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) :
    P + L ≤ C.output := by
  by_contra hout
  have hb : WireBelowOutput (P + L) C C.output := by
    intro z hz
    exact hz
  exact no_input_below P L I C hF C.output (by omega) hb

end PEqualNP.Outside.L_meta_2583_aux
