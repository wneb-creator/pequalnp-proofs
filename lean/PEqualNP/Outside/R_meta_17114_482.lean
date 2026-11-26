import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.GetD
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 1000000 in
theorem PEqualNP.Outside.R_meta_17114_482
    (extreme :
      let edge := fun u v : Fin 7 =>
        ¬(1 ≤ v.val ∧ v.val ≤ 3) ∧ (u = v ∨ u = v + 1 ∨ u = v + 3)
      ∃ C : Circuit, C.size ≤ 15 ∧ 25 ≤ C.output ∧ C.output < 25 + C.size ∧
        (∀ j g, C.gates[j]? = some g →
          (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
          ∃ a b, g.inputs = [a, b] ∧ a ≠ b ∧ a < 25 + j ∧ b < 25 + j) ∧
        (∀ u v, edge u v →
          C.eval (List.ofFn (fun i : Fin 14 =>
            decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 v)) ++
            List.replicate 11 false) = true) ∧
        (∀ b0 b4 b5 b6 : Bool,
          let right : Fin 7 → Bool := ![b0, true, true, true, b4, b5, b6]
          let left : Fin 7 → Bool := fun u => !decide (∃ v, edge u v ∧ right v = true)
          C.eval (List.ofFn (Fin.addCases left right) ++ List.replicate 11 true) = false) ∧
        ∀ t : Bool, ∃ p : ℕ → ℕ, p (if t = true then 0 else 7) = 0 ∧
          p (if t = true then 7 else 0) ≤ 1 ∧
          (∀ j < 25, j ≠ 0 → j ≠ 7 → p j = 2) ∧ 2 ≤ p C.output ∧
          ∀ j g a b, C.gates[j]? = some g → g.inputs = [a, b] →
            (g.op = GateOp.and → p (25 + j) ≤ p a + p b) ∧
            (g.op = GateOp.or → p (25 + j) ≤ min (p a) (p b)))
    (mono : ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ x y : List Bool, x.length = y.length →
        (∀ i : ℕ, x.getD i false = true → y.getD i false = true) →
        C.eval x = true → C.eval y = true) :
    ∃ (x1 : PEqualNP.CircuitLowerBounds.Circuit), x1.size ≤ (15 : ℕ) ∧ (25 : ℕ) ≤ x1.output ∧ x1.output < (25 : ℕ) + x1.size ∧ (∀ (x2 : ℕ) (x3 : PEqualNP.CircuitLowerBounds.Gate), x1.gates[x2]? = Option.some x3 → (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x5 : ℕ) (x6 : ℕ), x3.inputs = [x5, x6] ∧ x5 ≠ x6 ∧ x5 < (25 : ℕ) + x2 ∧ x6 < (25 : ℕ) + x2) ∧ (∀ (x2 : Fin (14 : ℕ) → Bool) (x3 : List Bool), x3.length = (11 : ℕ) → (x1.eval (List.ofFn x2 ++ x3) = Bool.true ↔ ∃ (x5 : Fin (7 : ℕ)) (x6 : Fin (7 : ℕ)), ¬((1 : ℕ) ≤ ↑x6 ∧ ↑x6 ≤ (3 : ℕ)) ∧ (x5 = x6 ∨ x5 = x6 + (1 : Fin (7 : ℕ)) ∨ x5 = x6 + (3 : Fin (7 : ℕ))) ∧ x2 (Fin.castAdd (7 : ℕ) x5) = Bool.true ∧ x2 (Fin.natAdd (7 : ℕ) x6) = Bool.true)) ∧ ∀ (x2 : Bool), ∃ (x3 : ℕ → ℕ), x3 (if x2 = Bool.true then (0 : ℕ) else (7 : ℕ)) = (0 : ℕ) ∧ x3 (if x2 = Bool.true then (7 : ℕ) else (0 : ℕ)) ≤ (1 : ℕ) ∧ (∀ x4 < (25 : ℕ), x4 ≠ (0 : ℕ) → x4 ≠ (7 : ℕ) → x3 x4 = (2 : ℕ)) ∧ (2 : ℕ) ≤ x3 x1.output ∧ ∀ (x4 : ℕ) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 x7 : ℕ), x1.gates[x4]? = Option.some x5 → x5.inputs = [x6, x7] → (x5.op = PEqualNP.CircuitLowerBounds.GateOp.and → x3 ((25 : ℕ) + x4) ≤ x3 x6 + x3 x7) ∧ (x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → x3 ((25 : ℕ) + x4) ≤ Min.min (x3 x6) (x3 x7)) := by
  obtain ⟨C, hsize, hlo, hhi, hlegal, hpos, hneg, hw⟩ := extreme
  refine ⟨C, hsize, hlo, hhi, hlegal, ?_, hw⟩
  have hops : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hg
    exact (hlegal j g hj).1
  let edge := fun u v : Fin 7 =>
    ¬(1 ≤ v.val ∧ v.val ≤ 3) ∧ (u = v ∨ u = v + 1 ∨ u = v + 3)
  intro x extra hlen
  constructor
  · intro hout
    by_contra hmiss
    let right : Fin 7 → Bool := ![x 7, true, true, true, x 11, x 12, x 13]
    let left : Fin 7 → Bool := fun u => !decide (∃ v, edge u v ∧ right v = true)
    let top : Fin 14 → Bool := fun i => Fin.addCases (m := 7) (n := 7) left right i
    have hright (v : Fin 7) : x (Fin.natAdd 7 v) = true → right v = true := by
      fin_cases v <;> intro hv <;> first | exact hv | rfl
    have hrightEdge (u v : Fin 7) (h : edge u v) :
        right v = x (Fin.natAdd 7 v) := by
      fin_cases v
      · rfl
      · exact (h.1 (by decide)).elim
      · exact (h.1 (by decide)).elim
      · exact (h.1 (by decide)).elim
      · rfl
      · rfl
      · rfl
    have hcover (i : Fin 14) : x i = true → top i = true := by
      refine Fin.addCases (m := 7) (n := 7)
        (motive := fun j => x j = true → top j = true) (fun u => ?_) (fun v => ?_) i
      · intro hu
        simp only [top, Fin.addCases_left, left, Bool.not_eq_true', decide_eq_false_iff_not]
        rintro ⟨v, hv, hr⟩
        exact hmiss ⟨u, v, hv.1, hv.2, hu, (hrightEdge u v hv).symm.trans hr⟩
      · simpa only [top, Fin.addCases_right] using hright v
    have hfalse : C.eval (List.ofFn top ++ List.replicate 11 true) = false :=
      hneg (x 7) (x 11) (x 12) (x 13)
    have htrue : C.eval (List.ofFn top ++ List.replicate 11 true) = true := by
      apply mono C hops (List.ofFn x ++ extra) _ (by simp [hlen]) _ hout
      intro i hi
      by_cases hj : i < 14
      · have h1 : i < (List.ofFn x).length := by simpa
        have h2 : i < (List.ofFn top).length := by simpa
        rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1,
          List.getElem_ofFn] at hi
        rw [List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2,
          List.getElem_ofFn]
        exact hcover ⟨i, hj⟩ hi
      · have h1 : (List.ofFn x).length ≤ i := by simpa using Nat.le_of_not_gt hj
        have h2 : (List.ofFn top).length ≤ i := by simpa using Nat.le_of_not_gt hj
        rw [List.getD_append_right _ _ _ _ h1] at hi
        rw [List.getD_append_right _ _ _ _ h2, List.length_ofFn]
        rw [List.length_ofFn] at hi
        by_cases hk : i - 14 < 11
        · exact List.getD_replicate true hk
        · have hbad : extra.getD (i - 14) false = false :=
            List.getD_eq_default _ _ (by omega)
          rw [hbad] at hi
          contradiction
    rw [hfalse] at htrue
    contradiction
  · rintro ⟨u, v, hne, hadj, hu, hv⟩
    let edgeInput : Fin 14 → Bool :=
      fun i => decide (i = Fin.castAdd 7 u ∨ i = Fin.natAdd 7 v)
    have htrue : C.eval (List.ofFn edgeInput ++ List.replicate 11 false) = true :=
      hpos u v ⟨hne, hadj⟩
    apply mono C hops _ (List.ofFn x ++ extra) (by simp [hlen]) _ htrue
    intro i hi
    by_cases hj : i < 14
    · have h1 : i < (List.ofFn edgeInput).length := by simpa
      have h2 : i < (List.ofFn x).length := by simpa
      rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1,
        List.getElem_ofFn] at hi
      rw [List.getD_append _ _ _ _ h2, List.getD_eq_getElem _ _ h2,
        List.getElem_ofFn]
      have he : (⟨i, hj⟩ : Fin 14) = Fin.castAdd 7 u ∨
          (⟨i, hj⟩ : Fin 14) = Fin.natAdd 7 v := of_decide_eq_true hi
      rcases he with h | h
      · exact h ▸ hu
      · exact h ▸ hv
    · have h1 : (List.ofFn edgeInput).length ≤ i := by simpa using Nat.le_of_not_gt hj
      rw [List.getD_append_right _ _ _ _ h1] at hi
      have hbad : false = true := by
        simpa only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq] using hi
      contradiction
