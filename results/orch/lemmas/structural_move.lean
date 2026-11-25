import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884_aux.Move

open PEqualNP.CircuitLowerBounds

def redirect (m a i : ℕ) : ℕ :=
  if i < m then i else if i = m then a else i - 1

lemma redirect_of_lt (m a i : ℕ) (hi : i < m) : redirect m a i = i := by
  simp [redirect, hi]

lemma redirect_at (m a : ℕ) : redirect m a m = a := by
  simp [redirect]

lemma redirect_of_gt (m a i : ℕ) (hi : m < i) : redirect m a i = i - 1 := by
  simp [redirect, show ¬i < m by omega, show i ≠ m by omega]

lemma redirect_lt_length (m a l i : ℕ) (ha : a < m) (hm : m ≤ l)
    (hi : i < l + 1) : redirect m a i < l := by
  unfold redirect
  split_ifs <;> omega

lemma alias_start (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ∀ i, (w ++ [w.getD a false]).getD i false =
      w.getD (redirect w.length a i) false := by
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi, redirect_of_lt _ _ _ hi]
  · by_cases he : i = w.length
    · subst i
      rw [redirect_at, List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · have hg : w.length < i := by omega
      rw [redirect_of_gt _ _ _ hg]
      rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by omega)]

lemma alias_extend (m a : ℕ) (v w : List Bool) (b : Bool)
    (ha : a < m) (hm : m ≤ w.length) (hlen : v.length = w.length + 1)
    (agree : ∀ i, v.getD i false = w.getD (redirect m a i) false) :
    ∀ i, (v ++ [b]).getD i false = (w ++ [b]).getD (redirect m a i) false := by
  intro i
  by_cases hi : i < v.length
  · have hr : redirect m a i < w.length :=
      redirect_lt_length m a w.length i ha hm (by omega)
    rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ hr]
    exact agree i
  · by_cases he : i = v.length
    · subst i
      have hg : m < v.length := by omega
      rw [redirect_of_gt _ _ _ hg]
      have hv : v.length - 1 = w.length := by omega
      rw [hv, List.getD_append_right _ _ _ _ (le_refl _),
        List.getD_append_right _ _ _ _ (le_refl _)]
      simp
    · have hg : m < i := by omega
      rw [redirect_of_gt _ _ _ hg,
        List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

def renameGate (m a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (redirect m a)⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma alias_gate (m a : ℕ) (v w : List Bool) (g : Gate)
    (agree : ∀ i, v.getD i false = w.getD (redirect m a i) false) :
    g.op.eval (g.inputs.map fun i => v.getD i false) =
      (renameGate m a g).op.eval
        ((renameGate m a g).inputs.map fun i => w.getD i false) := by
  simp only [renameGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact agree i

lemma alias_fold (m a : ℕ) (gs : List Gate) (v w : List Bool)
    (ha : a < m) (hm : m ≤ w.length) (hlen : v.length = w.length + 1)
    (agree : ∀ i, v.getD i false = w.getD (redirect m a i) false) :
    ∀ i, (gs.foldl step v).getD i false =
      ((gs.map (renameGate m a)).foldl step w).getD (redirect m a i) false := by
  induction gs generalizing v w with
  | nil => exact agree
  | cons g gs ih =>
    simp only [List.foldl_cons, List.map_cons]
    apply ih
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · simp only [step, List.length_append, List.length_singleton]
      omega
    · have hg := alias_gate m a v w g agree
      unfold step
      rw [← hg]
      exact alias_extend m a v w _ ha hm hlen agree

end PEqualNP.Outside.L_meta_1884_aux.Move
