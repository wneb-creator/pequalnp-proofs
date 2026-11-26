import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17972

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def Rel (w w' : List Bool) : Prop := w.length = w'.length ∧ ∀ i, w.getD i false = true → w'.getD i false = true

theorem getD_snoc (w : List Bool) (b : Bool) (i : ℕ) :
    (w ++ [b]).getD i false = if i < w.length then w.getD i false else if i = w.length then b else false := by
  rcases Nat.lt_or_ge i w.length with h | h
  · simp [h, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rcases Nat.eq_or_lt_of_le h with h | h
    · subst h; simp [List.getD_eq_getElem?_getD]
    · have h1 : ¬ i < w.length := by omega
      have h2 : i ≠ w.length := by omega
      simp only [h1, h2, if_false]
      rw [List.getD_eq_default]
      simp; omega

theorem eval_mono (g : Gate) (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (w w' : List Bool) (h : Rel w w')
    (he : g.op.eval (g.inputs.map fun i => w.getD i false) = true) :
    g.op.eval (g.inputs.map fun i => w'.getD i false) = true := by
  rcases hg with hg | hg <;> rw [hg] at he ⊢ <;> simp only [GateOp.eval, List.all_map, List.any_map, List.all_eq_true, List.any_eq_true, Function.comp, id] at he ⊢
  · intro i hi; exact h.2 i (he i hi)
  · obtain ⟨i, hi, hv⟩ := he; exact ⟨i, hi, h.2 i hv⟩

theorem fold_mono : ∀ (gs : List Gate), (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) →
    ∀ w w' : List Bool, Rel w w' →
    Rel (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w')
  | [], _, w, w', h => h
  | g :: gs, hg, w, w', h => by
    simp only [List.foldl_cons]
    apply fold_mono gs (fun x hx => hg x (List.mem_cons_of_mem _ hx))
    refine ⟨by simp [h.1], ?_⟩
    intro i hi
    rw [getD_snoc] at hi ⊢
    rw [← h.1]
    split_ifs at hi ⊢ with h1 h2
    · exact h.2 i hi
    · exact eval_mono g (hg g (List.mem_cons_self ..)) w w' h hi

theorem aux : True := trivial

end PEqualNP.Outside.L_meta_17972

theorem PEqualNP.Outside.L_meta_17972 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), (∀ x2 ∈ x1.gates, x2.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x2.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∀ (x3 x4 : List Bool), x3.length = x4.length → (∀ (x6 : ℕ), x3.getD x6 Bool.false = Bool.true → x4.getD x6 Bool.false = Bool.true) → x1.eval x3 = Bool.true → x1.eval x4 = Bool.true := by
  intro x1 hop x3 x4 hl hle h
  have hop' : ∀ g ∈ x1.gates, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and, PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) := by
    intro g hg
    rcases hop g hg with e | e <;> simp [e]
  exact (L_meta_17972.fold_mono x1.gates hop' x3 x4 ⟨hl, hle⟩).2 x1.output h
