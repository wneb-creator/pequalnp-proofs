import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_17757 : (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : List ℕ), PEqualNP.MetaComplexity.Monotone2 x1 → x2.length ≤ (2 : ℕ) → (∀ (x5 x6 : Finset (Fin (13 : ℕ))), PEqualNP.CircuitLowerBounds.GateOp.and.eval (List.map (fun (x7 : ℕ) => (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => if ↑x8 < (13 : ℕ) then Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x5) else Decidable.decide (Fin.ofNat (13 : ℕ) ↑x8 ∈ x6))).getD x7 Bool.false) x2) = Bool.true ↔ ∃ x7 ∈ x5, ∃ x8 ∈ x6, (↑x7 + ↑x8) % (13 : ℕ) ∈ [(0 : ℕ), (1 : ℕ), (3 : ℕ), (9 : ℕ)]) → x1.size = (0 : ℕ) → (63 : ℕ) ≤ x1.size) := by
  rintro ⟨gs, out⟩ ins _ _ correct size
  have hg : gs = [] := List.length_eq_zero_iff.mp size
  subst gs
  let row (p l : Finset (Fin 13)) := List.ofFn fun k : Fin 26 =>
    if k.val < 13 then decide (Fin.ofNat 13 k.val ∈ p) else decide (Fin.ofNat 13 k.val ∈ l)
  have hit (p l : Finset (Fin 13)) (h : ∃ u ∈ p, ∃ v ∈ l, (u.val + v.val) % 13 ∈ [0,1,3,9]) :
      ∀ i ∈ ins, (row p l).getD i false = true := by
    have yes := (correct p l).2 h
    change ((ins.map fun i => (row p l).getD i false).all id) = true at yes
    simpa using yes
  have h0 := hit {0} {0} ⟨0, by simp, 0, by simp, by decide⟩
  have h1 := hit {1} {2} ⟨1, by simp, 2, by simp, by decide⟩
  have disjoint : ∀ i : Fin 26, (row {0} {0}).getD i false = true →
      (row {1} {2}).getD i false = false := by decide
  have empty : ins = [] := by
    cases ins with
    | nil => rfl
    | cons i tail =>
      have a := h0 i (by simp)
      have b := h1 i (by simp)
      by_cases hi : i < 26
      · exact False.elim (Bool.false_ne_true ((disjoint ⟨i, hi⟩ a).symm.trans b))
      · have bound : (row {0} {0}).length ≤ i := by simpa [row] using Nat.le_of_not_gt hi
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none bound] at a
        contradiction
  subst ins
  have bad := (correct ∅ ∅).1 (by rfl)
  simpa using bad
