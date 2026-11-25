import PEqualNP.Defs

namespace PEqualNP.Outside.Pilot110ReaderBridge

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma append_agree_except (u : ℕ) (w z : List Bool) (b c : Bool)
    (lengths : w.length = z.length)
    (agree : ∀ i, i ≠ u → w.getD i false = z.getD i false) (same : b = c) :
    ∀ i, i ≠ u → (w ++ [b]).getD i false = (z ++ [c]).getD i false := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
    exact agree i hi
  · by_cases heq : i = w.length
    · subst i
      rw [show (w ++ [b]).getD w.length false = b by simp, lengths]
      simpa using same
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma fold_agree_except (u : ℕ) (gs : List Gate)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ u) (w z : List Bool)
    (lengths : w.length = z.length)
    (agree : ∀ i, i ≠ u → w.getD i false = z.getD i false) :
    ∀ i, i ≠ u → (gs.foldl step w).getD i false = (gs.foldl step z).getD i false := by
  induction gs generalizing w z with
  | nil => exact agree
  | cons g gs ih =>
    have same : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => z.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact agree i (avoid g (by simp) i hi)
    exact ih (fun q hq => avoid q (List.mem_cons_of_mem g hq))
      (step w g) (step z g) (by simp [step, lengths])
      (append_agree_except u w z _ _ lengths agree same)

lemma ofFn_agree_except {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ u → x i = y i) :
    ∀ i, i ≠ u.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn]
    exact agree ⟨i,hlt⟩ (fun h => hi (congrArg Fin.val h))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)]

lemma first_gate_masks_unique_read {n : ℕ} (u v : Fin n) (g : Gate) (gs : List Gate)
    (pins : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (b : Bool) (control : (g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true))
    (avoid : ∀ q ∈ gs, ∀ i ∈ q.inputs, i ≠ u.val)
    (out : ℕ) (out_ne : out ≠ u.val) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ u → x i = y i) (xv : x v = b) (yv : y v = b) :
    (Circuit.mk (g :: gs) out).eval (List.ofFn x) =
      (Circuit.mk (g :: gs) out).eval (List.ofFn y) := by
  have masked (z : Fin n → Bool) (hz : z v = b) :
      g.op.eval (g.inputs.map fun i => (List.ofFn z).getD i false) = b := by
    rcases pins with hp | hp <;> rcases control with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ <;>
      simp [hp, hop, GateOp.eval, hz]
  have initial := append_agree_except u.val (List.ofFn x) (List.ofFn y) _ _
    (by simp) (ofFn_agree_except u x y agree) ((masked x xv).trans (masked y yv).symm)
  exact fold_agree_except u.val gs avoid (step (List.ofFn x) g) (step (List.ofFn y) g)
    (by simp [step]) initial out out_ne

lemma first_gate_must_read_again {n : ℕ} (f : (Fin n → Bool) → Bool)
    (u v : Fin n) (g : Gate) (gs : List Gate) (out : ℕ)
    (pins : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (b : Bool) (control : (g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true))
    (out_ne : out ≠ u.val)
    (essential : ∃ x y : Fin n → Bool, (∀ i, i ≠ u → x i = y i) ∧
      x v = b ∧ y v = b ∧ f x ≠ f y)
    (computes : ∀ x : Fin n → Bool, (Circuit.mk (g :: gs) out).eval (List.ofFn x) = f x) :
    ∃ q ∈ gs, u.val ∈ q.inputs := by
  by_contra h
  have avoid : ∀ q ∈ gs, ∀ i ∈ q.inputs, i ≠ u.val := by
    intro q hq i hi eq
    subst i
    exact h ⟨q,hq,hi⟩
  obtain ⟨x,y,agree,xv,yv,different⟩ := essential
  have same := first_gate_masks_unique_read u v g gs pins b control avoid out out_ne x y agree xv yv
  rw [computes x, computes y] at same
  exact different same

end PEqualNP.Outside.Pilot110ReaderBridge
