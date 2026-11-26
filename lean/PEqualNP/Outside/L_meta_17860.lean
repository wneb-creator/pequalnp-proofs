import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17860
-- Wire induction adapted from L-meta-5470.
open PEqualNP.CircuitLowerBounds

theorem getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem all_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).all id = true → (l.map g).all id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id]
    exact fun ⟨h1, h2⟩ => ⟨h a h1, ih h2⟩

theorem any_mono (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i, f i = true → g i = true) :
    (l.map f).any id = true → (l.map g).any id = true := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.any_cons, Bool.or_eq_true, id]
    rintro (h1 | h2)
    · exact Or.inl (h a h1)
    · exact Or.inr (ih h2)

theorem mono : ∀ (gs : List Gate) (W1 W2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → W1.length = W2.length →
    (∀ w, W1.getD w false = true → W2.getD w false = true) →
    ∀ w, (gs.foldl wstep W1).getD w false = true → (gs.foldl wstep W2).getD w false = true := by
  intro gs
  induction gs with
  | nil => intro W1 W2 _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 hop hl h
    simp only [List.foldl_cons]
    apply ih
    · exact fun g' hg' => hop g' (List.mem_cons_of_mem _ hg')
    · simp [wstep, hl]
    · intro w hw
      simp only [wstep] at hw ⊢
      rw [getD_snoc] at hw
      rw [getD_snoc, ← hl]
      by_cases c1 : w < W1.length
      · rw [if_pos c1] at hw ⊢; exact h w hw
      · rw [if_neg c1] at hw ⊢
        by_cases c2 : w = W1.length
        · rw [if_pos c2] at hw ⊢
          rcases hop g List.mem_cons_self with e | e
          · rw [e] at hw ⊢
            exact all_mono _ _ _ h hw
          · rw [e] at hw ⊢
            exact any_mono _ _ _ h hw
        · rw [if_neg c2] at hw; exact absurd hw (by decide)

theorem monotone {n : ℕ} (C : Circuit) (ao : PEqualNP.TopForm.IsAO2 n C)
    (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    C.eval (List.ofFn x) = true → C.eval (List.ofFn y) = true := by
  apply mono C.gates _ _ ao.1 (by simp) _ C.output
  intro w
  by_cases hw : w < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw] using h ⟨w, hw⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw]
end PEqualNP.Outside.L_meta_17860

theorem PEqualNP.Outside.L_meta_17860 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (14 : ℕ) x1 → ∀ (x3 x4 : Fin (14 : ℕ) → Bool), (∀ (x5 : Fin (14 : ℕ)), x3 x5 = Bool.true → x4 x5 = Bool.true) → x1.eval (List.ofFn x3) = Bool.true → x1.eval (List.ofFn x4) = Bool.true := by
  intro C ao x y h
  exact PEqualNP.Outside.L_meta_17860.monotone C ao x y h
