import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17701
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi


end PEqualNP.Outside.L_meta_17701

open PEqualNP.Outside.L_meta_17701 in
theorem PEqualNP.Outside.L_meta_17701 :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool) (x5 : ℕ), (∀ (x6 : Fin (14 : ℕ)), x3 x6 = Bool.true → x4 x6 = Bool.true) → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x3 x5 = Bool.true → PEqualNP.BlindGate.wireValue x1 (14 : ℕ) x4 x5 = Bool.true) := by
  intro C hC x y w xy hx
  have hInputs : LeL (List.ofFn x) (List.ofFn y) := by
    intro i hi
    by_cases h : i < 14
    · rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn] at hi ⊢
      exact xy ⟨i, h⟩ hi
    · have hlen : (List.ofFn x).length ≤ i := by simpa using (Nat.le_of_not_gt h)
      rw [List.getD_eq_default _ _ hlen] at hi
      contradiction
  exact fold_mono C.gates hC.1 _ _ (by simp) hInputs w hx