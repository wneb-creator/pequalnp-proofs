import Mathlib.Data.List.Forall2
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma read_le {w v : List Bool} (h : List.Forall₂ (· ≤ ·) w v) (i : ℕ) :
    w.getD i false ≤ v.getD i false := by
  induction h generalizing i with
  | nil => simp
  | cons hab h ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma eval_true_mono (op : GateOp) (hop : op = .and ∨ op = .or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · intro hf
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hf ⊢
    rintro b ⟨i, hi, rfl⟩
    exact h i hi (hf _ ⟨i, hi, rfl⟩)
  · intro hf
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hf ⊢
    obtain ⟨b, ⟨i, hi, rfl⟩, hb⟩ := hf
    exact ⟨_, ⟨i, hi, rfl⟩, h i hi hb⟩

lemma eval_le (op : GateOp) (hop : op = .and ∨ op = .or) (l : List ℕ)
    (f g : ℕ → Bool) (h : ∀ i, f i ≤ g i) :
    op.eval (l.map f) ≤ op.eval (l.map g) := by
  have hm := eval_true_mono op hop l f g (fun i _ hi => by
    have := h i
    cases hg : g i <;> simp_all [Bool.le_iff_imp])
  cases hf : op.eval (l.map f) <;> cases hg : op.eval (l.map g) <;>
    simp_all [Bool.le_iff_imp]

lemma run_le (gs : List Gate) (hg : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {w v : List Bool} (h : List.Forall₂ (· ≤ ·) w v) :
    List.Forall₂ (· ≤ ·) (run gs w) (run gs v) := by
  induction gs generalizing w v with
  | nil => exact h
  | cons g gs ih =>
    have hop := hg g (by simp)
    have hb := eval_le g.op hop g.inputs
      (fun i => w.getD i false) (fun i => v.getD i false) (read_le h)
    have hs : List.Forall₂ (· ≤ ·) (step w g) (step v g) :=
      List.rel_append h (.cons hb .nil)
    exact ih (fun a ha => hg a (by simp [ha])) hs

lemma circuit_le (C : Circuit) (hm : Monotone2 C)
    {w v : List Bool} (h : List.Forall₂ (· ≤ ·) w v) : C.eval w ≤ C.eval v := by
  apply read_le (run_le C.gates ?_ h) C.output
  intro g hg
  have ho := (hm g hg).1
  simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using ho

lemma suffix_bit_le (C : Circuit) (hm : Monotone2 C) (w : List Bool) :
    C.eval (w ++ [false]) ≤ C.eval (w ++ [true]) := by
  have hw : List.Forall₂ (· ≤ ·) w w := by
    induction w with
    | nil => exact .nil
    | cons b bs ih => exact .cons le_rfl ih
  exact circuit_le C hm (List.rel_append hw (.cons (by decide) .nil))

lemma replace_not_from_below {α : Type} (F g : α → Bool) (w : α → List Bool)
    (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x, F x = C.eval (w x ++ [!(g x)]))
    (below : ∀ x, g x ≤ F x) :
    ∀ x, C.eval (w x ++ [true]) = F x := by
  intro x
  have hle := suffix_bit_le C hm (w x)
  have hc := correct x
  have hb := below x
  cases hg : g x <;> cases hf : F x <;> simp_all [Bool.le_iff_imp]

lemma replace_not_from_above {α : Type} (F g : α → Bool) (w : α → List Bool)
    (C : Circuit) (hm : Monotone2 C)
    (correct : ∀ x, F x = C.eval (w x ++ [!(g x)]))
    (above : ∀ x, F x ≤ g x) :
    ∀ x, C.eval (w x ++ [false]) = F x := by
  intro x
  have hle := suffix_bit_le C hm (w x)
  have hc := correct x
  have ha := above x
  cases hg : g x <;> cases hf : F x <;> simp_all [Bool.le_iff_imp]

end PEqualNP.Outside.L_meta_2592_aux.OneNot
