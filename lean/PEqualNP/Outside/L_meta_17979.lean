import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17979
open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Split (a b c : List Bool) : Prop :=
  ∀ i, c.getD i false = true → a.getD i false = true ∨ b.getD i false = true

theorem foldSplit (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .or) :
    ∀ a b c : List Bool, a.length = c.length → b.length = c.length → Split a b c →
      Split (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs with
  | nil => intro a b c _ _ h; exact h
  | cons g gs ih =>
    intro a b c ha hb hs
    simp only [List.foldl_cons]
    apply ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
    · simp [step, ha]
    · simp [step, hb]
    · intro i hi
      unfold step at hi ⊢
      by_cases h : i < c.length
      · rw [List.getD_append _ _ _ _ h] at hi
        rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hs i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega), ha, hb]
        by_cases hz : i - c.length = 0
        · rw [hz] at hi ⊢
          simp only [List.getD_cons_zero, hg g List.mem_cons_self, GateOp.eval,
            List.any_map, Function.comp_apply, id_eq, List.any_eq_true] at hi ⊢
          obtain ⟨j, hj, hv⟩ := hi
          rcases hs j hv with h' | h'
          · exact Or.inl ⟨j, hj, h'⟩
          · exact Or.inr ⟨j, hj, h'⟩
        · obtain ⟨k, hk⟩ : ∃ k, i - c.length = k + 1 := ⟨i - c.length - 1, by omega⟩
          rw [hk] at hi
          simp at hi

def leftOnly (i : Fin 26) : Bool := decide (i = 1)
def rightOnly (i : Fin 26) : Bool := decide (i = 14)
def pair (i : Fin 26) : Bool := leftOnly i || rightOnly i

theorem pairSplit : Split (List.ofFn leftOnly) (List.ofFn rightOnly) (List.ofFn pair) := by
  intro i hi
  by_cases h : i < 26
  · rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn] at hi
    rw [List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn,
        List.getD_eq_getElem _ _ (by simp; exact h), List.getElem_ofFn]
    simpa [pair] using hi
  · rw [List.getD_eq_default _ _ (by simpa using (Nat.le_of_not_gt h))] at hi
    contradiction

end PEqualNP.Outside.L_meta_17979

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_17979 in
theorem PEqualNP.Outside.L_meta_17979 :
  (∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x1 → (∀ (x3 : Fin (26 : ℕ) → Bool), x1.eval (List.ofFn x3) = Bool.true ↔ ∃ (x4 : Fin (13 : ℕ)) (x5 : Fin (13 : ℕ)), (x4 = x5 ∨ x4 = x5 + (1 : Fin (13 : ℕ)) ∨ x4 = x5 + (3 : Fin (13 : ℕ)) ∨ x4 = x5 + (9 : Fin (13 : ℕ))) ∧ x4 ≠ (0 : Fin (13 : ℕ)) ∧ x3 (Fin.castAdd (13 : ℕ) x4) = Bool.true ∧ x3 (Fin.natAdd (13 : ℕ) x5) = Bool.true) → (¬∃ (x4 : Fin x1.gates.length), (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.and) → (59 : ℕ) ≤ x1.size) := by
  intro C hao hf hno
  have hor : ∀ g ∈ C.gates, g.op = .or := by
    intro g hg
    rcases hao.1 g hg with ha | ho
    · obtain ⟨i, hi⟩ := List.getElem_of_mem hg
      exact (hno ⟨⟨i, hi.1⟩, by simpa [hi.2] using ha⟩).elim
    · exact ho
  have hleft : C.eval (List.ofFn leftOnly) ≠ true := by
    intro h
    obtain ⟨p, l, _, _, _, hl⟩ := (hf leftOnly).mp h
    have he : Fin.natAdd 13 l = (1 : Fin 26) := by simpa [leftOnly] using hl
    have hv := congrArg Fin.val he
    simp at hv <;> omega
  have hright : C.eval (List.ofFn rightOnly) ≠ true := by
    intro h
    obtain ⟨p, l, _, _, hp, _⟩ := (hf rightOnly).mp h
    have he : Fin.castAdd 13 p = (14 : Fin 26) := by simpa [rightOnly] using hp
    have hv := congrArg Fin.val he
    simp at hv <;> omega
  have hpair : C.eval (List.ofFn pair) = true := (hf pair).mpr ⟨1, 1, by decide, by decide, by decide, by decide⟩
  rcases foldSplit C.gates hor _ _ _ (by simp) (by simp) pairSplit C.output hpair with h | h
  · exact (hleft h).elim
  · exact (hright h).elim
