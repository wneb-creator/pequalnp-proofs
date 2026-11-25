import PEqualNP.Defs.ReadK

namespace PEqualNP.Outside.L_meta_2602_aux

open PEqualNP.CircuitLowerBounds

def repeatWrap (n : ℕ) (C : Circuit) (z : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, z]⟩, ⟨.and, [C.output, n + C.size]⟩],
    n + C.size + 1⟩

lemma repeatWrap_size (n : ℕ) (C : Circuit) (z : ℕ) :
    (repeatWrap n C z).size = C.size + 2 := by
  simp [repeatWrap, Circuit.size]

lemma repeatWrap_valid (n : ℕ) (C : Circuit) (z : ℕ)
    (ho : C.output < n + C.size) (hz : z < n + C.size) (hne : C.output ≠ z)
    (hC : ∀ j g, C.gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
        ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j) :
    ∀ j g, (repeatWrap n C z).gates[j]? = some g →
      (g.op = .and ∨ g.op = .or) ∧
        ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < n + j ∧ b < n + j := by
  intro j g hg
  change (C.gates ++ [⟨.or, [C.output, z]⟩,
    ⟨.and, [C.output, n + C.size]⟩])[j]? = some g at hg
  by_cases hj : j < C.gates.length
  · rw [List.getElem?_append_left hj] at hg
    exact hC j g hg
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hj)] at hg
    by_cases h0 : j = C.size
    · subst j
      simp only [Circuit.size, Nat.sub_self, List.getElem?_cons_zero] at hg
      cases hg
      exact ⟨Or.inr rfl, C.output, z, rfl, hne, ho, hz⟩
    · by_cases h1 : j = C.size + 1
      · subst j
        simp only [Circuit.size, Nat.add_sub_cancel_left, List.getElem?_cons_succ,
          List.getElem?_cons_zero] at hg
        cases hg
        exact ⟨Or.inl rfl, C.output, n + C.size, rfl, by omega, by omega, by omega⟩
      · have hfar : 2 ≤ j - C.gates.length := by dsimp [Circuit.size] at h0 h1; omega
        rw [List.getElem?_eq_none (by simpa using hfar)] at hg
        contradiction

lemma growingFold_length {α β : Type} (f : List α → β → α)
    (gs : List β) (w : List α) :
    (gs.foldl (fun s g => s ++ [f s g]) w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]
    omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  exact growingFold_length _ C.gates x

lemma repeatWrap_eval (n : ℕ) (C : Circuit) (z : ℕ) (x : List Bool)
    (hx : x.length = n) (ho : C.output < n + C.size) :
    (repeatWrap n C z).eval x = C.eval x := by
  let w := C.wires x
  have hw : w.length = n + C.size := by simp [w, wires_length, hx]
  have hout : C.output < w.length := by simpa [hw] using ho
  have old : (w ++ [w.getD C.output false || w.getD z false]).getD
      C.output false = w.getD C.output false :=
    List.getD_append _ _ _ _ hout
  have last : (w ++ [w.getD C.output false || w.getD z false]).getD
      (n + C.size) false = (w.getD C.output false || w.getD z false) := by
    rw [← hw, List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hcalc : (repeatWrap n C z).wires x =
      (w ++ [w.getD C.output false || w.getD z false]) ++
      [((w ++ [w.getD C.output false || w.getD z false]).getD C.output false &&
        (w ++ [w.getD C.output false || w.getD z false]).getD (n + C.size) false)] := by
    simp [repeatWrap, Circuit.wires, List.foldl_append, GateOp.eval, w]
  change ((repeatWrap n C z).wires x).getD (n + C.size + 1) false = w.getD C.output false
  rw [hcalc, old, last]
  rw [List.getD_append_right _ _ _ _ (by simp [hw])]
  simp [hw]
  exact fun h => Or.inl h

lemma linearParts_length (C : Circuit) (s : ℕ → Bool) (x : List Bool) :
    (PEqualNP.ReadK.linearParts C s x).length = x.length + C.size := by
  unfold PEqualNP.ReadK.linearParts Circuit.size
  rw [growingFold_length]
  simp

lemma repeatWrap_linear (n : ℕ) (C : Circuit) (z : ℕ) (s : ℕ → Bool)
    (x : List Bool) (hx : x.length = n) (ho : C.output < n + C.size)
    (hC : ((PEqualNP.ReadK.linearParts C s x).getD C.output (false, false)).1 = false)
    (hz : ((PEqualNP.ReadK.linearParts C s x).getD z (false, false)).1 = false) :
    ((PEqualNP.ReadK.linearParts (repeatWrap n C z) s x).getD
      (repeatWrap n C z).output (false, false)).2 = false := by
  let w := PEqualNP.ReadK.linearParts C s x
  let a := w.getD C.output (false, false)
  let b := w.getD z (false, false)
  let c := (a.1 || b.1, a.2 || b.2)
  have hw : w.length = n + C.size := by simp [w, linearParts_length, hx]
  have old : (w ++ [c]).getD C.output (false, false) = a :=
    List.getD_append _ _ _ _ (by simpa [hw] using ho)
  have last : (w ++ [c]).getD (n + C.size) (false, false) = c := by
    rw [← hw, List.getD_append_right _ _ _ _ (by omega)]
    simp
  have hcalc : PEqualNP.ReadK.linearParts (repeatWrap n C z) s x =
      (w ++ [c]) ++
      [(((w ++ [c]).getD C.output (false, false)).1 &&
          ((w ++ [c]).getD (n + C.size) (false, false)).1,
        (((w ++ [c]).getD C.output (false, false)).1 &&
          ((w ++ [c]).getD (n + C.size) (false, false)).2) ||
        (((w ++ [c]).getD C.output (false, false)).2 &&
          ((w ++ [c]).getD (n + C.size) (false, false)).1))] := by
    simp [repeatWrap, PEqualNP.ReadK.linearParts, List.foldl_append, w, a, b, c]
  change ((PEqualNP.ReadK.linearParts (repeatWrap n C z) s x).getD
    (n + C.size + 1) (false, false)).2 = false
  rw [hcalc, old, last]
  rw [List.getD_append_right _ _ _ _ (by simp [hw])]
  change a.1 = false at hC
  change b.1 = false at hz
  simp [hw, c, hC, hz]

end PEqualNP.Outside.L_meta_2602_aux
