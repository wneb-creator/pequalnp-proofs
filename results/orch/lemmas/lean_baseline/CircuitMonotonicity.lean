import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def bitImplies (a b : Bool) : Prop := a = true → b = true

lemma getD_bitImplies {xs ys : List Bool} (h : List.Forall₂ bitImplies xs ys)
    (i : ℕ) : bitImplies (xs.getD i false) (ys.getD i false) := by
  induction h generalizing i with
  | nil => simp [bitImplies]
  | @cons a b xs ys hab h ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

lemma gate_bitImplies (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : List.Forall₂ bitImplies xs ys) :
    bitImplies (g.op.eval (g.inputs.map fun i => xs.getD i false))
      (g.op.eval (g.inputs.map fun i => ys.getD i false)) := by
  rcases hg with hg | hg
  · simp only [hg, GateOp.eval, bitImplies, List.all_eq_true, List.mem_map]
    intro hx b hb
    rcases hb with ⟨i, hi, rfl⟩
    exact getD_bitImplies h i (hx _ ⟨i, hi, rfl⟩)
  · simp only [hg, GateOp.eval, bitImplies, List.any_eq_true, List.mem_map]
    rintro ⟨b, ⟨i, hi, rfl⟩, hb⟩
    exact ⟨_, ⟨i, hi, rfl⟩, getD_bitImplies h i hb⟩

lemma fold_bitImplies (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {xs ys : List Bool} (h : List.Forall₂ bitImplies xs ys) :
    List.Forall₂ bitImplies
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun k hk => hgs k (List.mem_cons_of_mem g hk))
    exact List.rel_append h (.cons (gate_bitImplies g (hgs g (by simp)) h) .nil)

theorem circuit_eval_bitImplies (C : Circuit) (hC : Monotone2 C)
    {xs ys : List Bool} (h : List.Forall₂ bitImplies xs ys) :
    bitImplies (C.eval xs) (C.eval ys) := by
  apply getD_bitImplies
  apply fold_bitImplies C.gates _ h
  intro g hg
  have hop := (hC g hg).1
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hop

end PEqualNP.Outside.L_meta_650
