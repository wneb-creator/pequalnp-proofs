import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18167

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) : (step w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem any_or (l : List ℕ) (f g : ℕ → Bool) :
    (l.any fun i => f i || g i) = (l.any f || l.any g) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons, ih]
    cases f a <;> cases g a <;> cases l.any f <;> cases l.any g <;> rfl

theorem add_run (gs : List Gate) : ∀ (w w1 w2 : List Bool),
    (∀ g ∈ gs, g.op = GateOp.or) → w.length = w1.length → w.length = w2.length →
    (∀ i, w.getD i false = (w1.getD i false || w2.getD i false)) →
    ∀ i, (gs.foldl step w).getD i false
      = ((gs.foldl step w1).getD i false || (gs.foldl step w2).getD i false) := by
  induction gs with
  | nil => intro w w1 w2 _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w1 w2 hall h1 h2 h
    simp only [List.foldl_cons]
    apply ih (step w g) (step w1 g) (step w2 g) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      (by simp [step, h1]) (by simp [step, h2])
    intro i
    rw [step_getD, step_getD, step_getD, ← h1, ← h2]
    split_ifs with c1 c2
    · exact h i
    · rw [hall g List.mem_cons_self]
      simp only [GateOp.eval, List.any_map]
      have : (fun i => w.getD i false) = fun i => (w1.getD i false || w2.getD i false) := funext h
      have e := any_or g.inputs (fun i => w1.getD i false) (fun i => w2.getD i false)
      simp only [Function.comp_def, id] at e ⊢
      rw [this]
      exact e
    · rfl

theorem addC (C : Circuit) (hor : ∀ g ∈ C.gates, g.op = GateOp.or) :
    C.eval (List.ofFn fun i : Fin 10 => decide (i = 0 ∨ i = 1))
      = (C.eval (List.ofFn fun i : Fin 10 => decide (i = 0)) ||
        C.eval (List.ofFn fun i : Fin 10 => decide (i = 1))) := by
  have hadd := add_run C.gates (List.ofFn fun i : Fin 10 => decide (i = 0 ∨ i = 1))
    (List.ofFn fun i : Fin 10 => decide (i = 0)) (List.ofFn fun i : Fin 10 => decide (i = 1))
    hor (by simp) (by simp)
    (by
      intro i
      rcases Nat.lt_or_ge i 10 with h | h
      · rw [List.getD_eq_getElem _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h),
          List.getD_eq_getElem _ _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        simp
      · rw [List.getD_eq_default _ _ (by simpa using h), List.getD_eq_default _ _ (by simpa using h),
          List.getD_eq_default _ _ (by simpa using h)]
        rfl) C.output
  exact hadd

end PEqualNP.Outside.L_meta_18167

theorem PEqualNP.Outside.L_meta_18167 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x1 → x1.size ≤ (18 : ℕ) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → ∃ (x5 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn x5) ≠ (x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) := by
  intro C hM hs hno
  by_contra hcon
  have h : ∀ x5 : Fin 10 → Bool, C.eval (List.ofFn x5) = (x5 (0 : Fin (10 : ℕ)) && x5 (1 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (2 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (3 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (4 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (0 : Fin (10 : ℕ)) || x5 (0 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ)) || x5 (1 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (2 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (3 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (4 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (5 : Fin (10 : ℕ)) && x5 (7 : Fin (10 : ℕ)) || x5 (7 : Fin (10 : ℕ)) && x5 (9 : Fin (10 : ℕ)) || x5 (9 : Fin (10 : ℕ)) && x5 (6 : Fin (10 : ℕ)) || x5 (6 : Fin (10 : ℕ)) && x5 (8 : Fin (10 : ℕ)) || x5 (8 : Fin (10 : ℕ)) && x5 (5 : Fin (10 : ℕ))) := by
    intro x5
    by_contra hne
    exact hcon ⟨x5, hne⟩
  have hor : ∀ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.or := by
    intro g hg
    have h1 := (hM g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    rcases h1 with h1 | h1
    · obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hg
      exact absurd ⟨j, h1⟩ hno
    · exact h1
  have hadd := PEqualNP.Outside.L_meta_18167.addC C hor
  have hA : C.eval (List.ofFn fun i : Fin 10 => decide (i = 0)) = false := by
    rw [h]; decide
  have hB : C.eval (List.ofFn fun i : Fin 10 => decide (i = 1)) = false := by
    rw [h]; decide
  have hAB : C.eval (List.ofFn fun i : Fin 10 => decide (i = 0 ∨ i = 1)) = true := by
    rw [h]; decide
  rw [hA, hB, hAB] at hadd
  exact Bool.noConfusion hadd
