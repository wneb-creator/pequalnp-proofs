import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_5166_317
    (cConst : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2;
      ∀ (c : Bool) (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (13 : ℕ) →
        ¬∀ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)), c]) = x1 x)
    (cDup : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2;
      ∀ (C : PEqualNP.CircuitLowerBounds.Circuit),
        PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (13 : ℕ) →
        (∀ i : Fin (9 : ℕ), ¬∀ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)), x i]) = x1 x) ∧
        ¬∀ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)), !x (0 : Fin (9 : ℕ))]) = x1 x)
    (cNotOr : have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2;
      ∀ (i : Fin (9 : ℕ)) (C : PEqualNP.CircuitLowerBounds.Circuit),
        i ≠ (0 : Fin (9 : ℕ)) → PEqualNP.MetaComplexity.FanInTwo C → C.size ≤ (13 : ℕ) →
        ¬∀ (x : Fin (9 : ℕ) → Bool), C.eval (List.ofFn x ++ [!x (0 : Fin (9 : ℕ)), !x (0 : Fin (9 : ℕ)) || x i]) = x1 x) :
    have x1 : (Fin (9 : ℕ) → Bool) → Bool := fun (x1 : Fin (9 : ℕ) → Bool) => [((0 : Fin (9 : ℕ)), (1 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (2 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (3 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (4 : Fin (9 : ℕ))), ((4 : Fin (9 : ℕ)), (0 : Fin (9 : ℕ))), ((0 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ))), ((1 : Fin (9 : ℕ)), (6 : Fin (9 : ℕ))), ((2 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((3 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((5 : Fin (9 : ℕ)), (7 : Fin (9 : ℕ))), ((6 : Fin (9 : ℕ)), (8 : Fin (9 : ℕ))), ((8 : Fin (9 : ℕ)), (5 : Fin (9 : ℕ)))].any fun (x2 : Fin (9 : ℕ) × Fin (9 : ℕ)) => x1 x2.1 && x1 x2.2; have x2 : Fin (9 : ℕ) → Fin (9 : ℕ) → PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 x3 : Fin (9 : ℕ)) (x4 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x5 : Fin (9 : ℕ) → Bool), x4.eval (List.ofFn x5 ++ [!x5 (0 : Fin (9 : ℕ)), x5 x2 || x5 x3]) = x1 x5; ∀ (x3 : List ℕ) (x4 : PEqualNP.CircuitLowerBounds.Circuit),   x3.length ≤ (2 : ℕ) →     PEqualNP.MetaComplexity.FanInTwo x4 →       x4.size ≤ (13 : ℕ) →         (∀ (x8 : Fin (9 : ℕ) → Bool),             have x9 : List Bool := List.ofFn x8 ++ [!x8 (0 : Fin (9 : ℕ))];             x4.eval (x9 ++ [PEqualNP.CircuitLowerBounds.GateOp.or.eval (List.map (fun (x10 : ℕ) => x9.getD x10 Bool.false) x3)]) = x1 x8) →           ∃ (x9 : Fin (9 : ℕ)) (x10 : Fin (9 : ℕ)), x9 < x10 ∧ x2 x9 x10 x4 := by
  intro x1 x2 x3 x4 hlen hfan hsize hev
  have huse : ∀ (f : (Fin 9 → Bool) → Bool),
      (∀ x : Fin 9 → Bool,
        PEqualNP.CircuitLowerBounds.GateOp.or.eval
          (List.map (fun k => (List.ofFn x ++ [!x 0]).getD k false) x3) = f x) →
      ∀ x : Fin 9 → Bool, x4.eval (List.ofFn x ++ [!x 0, f x]) = x1 x := by
    intro f hf x
    have hx := hev x
    dsimp only at hx
    rw [hf x, List.append_assoc] at hx
    exact hx
  have hor0 : PEqualNP.CircuitLowerBounds.GateOp.or.eval [] = false := rfl
  have hor1 : ∀ p : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [p] = p := by
    intro p; cases p <;> rfl
  have hor2 : ∀ p q : Bool, PEqualNP.CircuitLowerBounds.GateOp.or.eval [p, q] = (p || q) := by
    intro p q; cases p <;> cases q <;> rfl
  have hget : ∀ (x : Fin 9 → Bool) (k : ℕ),
      (List.ofFn x ++ [!x 0]).getD k false =
        if hk : k < 9 then x ⟨k, hk⟩ else if k = 9 then !x 0 else false := by
    intro x k
    simp only [List.getD_eq_getElem?_getD]
    by_cases hk : k < 9
    · have hlt : k < (List.ofFn x).length := by simp [hk]
      rw [List.getElem?_append_left hlt, List.getElem?_ofFn]
      simp [hk]
    · by_cases h9 : k = 9
      · subst h9
        rw [List.getElem?_append_right (by simp)]
        simp
      · rw [List.getElem?_eq_none (by simp; omega)]
        simp [hk, h9]
  cases x3 with
  | nil =>
    exact False.elim (cConst false x4 hfan hsize (huse _ (fun _ => hor0)))
  | cons a t =>
    cases t with
    | nil =>
      exfalso
      by_cases ha : a < 9
      · refine (cDup x4 hfan hsize).1 ⟨a, ha⟩ (huse _ (fun x => ?_))
        change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x ++ [!x 0]).getD a false] = x ⟨a, ha⟩
        rw [hor1, hget x a, dif_pos ha]
      · by_cases ha9 : a = 9
        · subst ha9
          refine (cDup x4 hfan hsize).2 (huse _ (fun x => ?_))
          change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x ++ [!x 0]).getD 9 false] = !x 0
          rw [hor1, hget x 9]
          rfl
        · refine cConst false x4 hfan hsize (huse _ (fun x => ?_))
          change PEqualNP.CircuitLowerBounds.GateOp.or.eval [(List.ofFn x ++ [!x 0]).getD a false] = false
          rw [hor1, hget x a, dif_neg ha, if_neg ha9]
    | cons b t2 =>
      cases t2 with
      | cons _ _ => simp at hlen
      | nil =>
        have hpair : ∀ x : Fin 9 → Bool,
            PEqualNP.CircuitLowerBounds.GateOp.or.eval
              (List.map (fun k => (List.ofFn x ++ [!x 0]).getD k false) [a, b]) =
            ((List.ofFn x ++ [!x 0]).getD a false || (List.ofFn x ++ [!x 0]).getD b false) :=
          fun x => hor2 _ _
        by_cases ha : a < 9
        · by_cases hb : b < 9
          · by_cases hab : a = b
            · subst hab
              refine False.elim ((cDup x4 hfan hsize).1 ⟨a, ha⟩ (huse _ (fun x => ?_)))
              rw [hpair x, hget x a, dif_pos ha, Bool.or_self]
            · by_cases hlt : a < b
              · refine ⟨⟨a, ha⟩, ⟨b, hb⟩, hlt, huse _ (fun x => ?_)⟩
                rw [hpair x, hget x a, hget x b, dif_pos ha, dif_pos hb]
              · refine ⟨⟨b, hb⟩, ⟨a, ha⟩, Fin.mk_lt_mk.mpr (by omega), huse _ (fun x => ?_)⟩
                rw [hpair x, hget x a, hget x b, dif_pos ha, dif_pos hb, Bool.or_comm]
          · exfalso
            by_cases hb9 : b = 9
            · subst hb9
              by_cases ha0 : a = 0
              · subst ha0
                refine cConst true x4 hfan hsize (huse _ (fun x => ?_))
                rw [hpair x, hget x 0, hget x 9]
                exact Bool.or_not_self (x 0)
              · refine cNotOr ⟨a, ha⟩ x4 (fun e => ha0 (congrArg Fin.val e)) hfan hsize (huse _ (fun x => ?_))
                rw [hpair x, hget x a, hget x 9, dif_pos ha]
                exact Bool.or_comm (x ⟨a, ha⟩) (!x 0)
            · refine (cDup x4 hfan hsize).1 ⟨a, ha⟩ (huse _ (fun x => ?_))
              rw [hpair x, hget x a, hget x b, dif_pos ha, dif_neg hb, if_neg hb9, Bool.or_false]
        · exfalso
          by_cases ha9 : a = 9
          · subst ha9
            by_cases hb : b < 9
            · by_cases hb0 : b = 0
              · subst hb0
                refine cConst true x4 hfan hsize (huse _ (fun x => ?_))
                rw [hpair x, hget x 9, hget x 0]
                exact Bool.not_or_self (x 0)
              · refine cNotOr ⟨b, hb⟩ x4 (fun e => hb0 (congrArg Fin.val e)) hfan hsize (huse _ (fun x => ?_))
                rw [hpair x, hget x 9, hget x b, dif_pos hb]
                rfl
            · by_cases hb9 : b = 9
              · subst hb9
                refine (cDup x4 hfan hsize).2 (huse _ (fun x => ?_))
                rw [hpair x, hget x 9]
                exact Bool.or_self (!x 0)
              · refine (cDup x4 hfan hsize).2 (huse _ (fun x => ?_))
                rw [hpair x, hget x 9, hget x b, dif_neg hb, if_neg hb9]
                exact Bool.or_false (!x 0)
          · by_cases hb : b < 9
            · refine (cDup x4 hfan hsize).1 ⟨b, hb⟩ (huse _ (fun x => ?_))
              rw [hpair x, hget x a, hget x b, dif_neg ha, if_neg ha9, dif_pos hb, Bool.false_or]
            · by_cases hb9 : b = 9
              · subst hb9
                refine (cDup x4 hfan hsize).2 (huse _ (fun x => ?_))
                rw [hpair x, hget x a, hget x 9, dif_neg ha, if_neg ha9]
                exact Bool.false_or (!x 0)
              · refine cConst false x4 hfan hsize (huse _ (fun x => ?_))
                rw [hpair x, hget x a, hget x b, dif_neg ha, if_neg ha9, dif_neg hb, if_neg hb9]
                rfl
