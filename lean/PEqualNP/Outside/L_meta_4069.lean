import Mathlib
import PEqualNP.Defs

-- AND and OR gates are monotone, so the wire values of a circuit built from them are
-- monotone in the input, by induction along the gate list.
namespace PEqualNP.Outside.L_meta_4069
open PEqualNP.CircuitLowerBounds

def W (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma W_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

lemma W_length (gs : List Gate) (x : List Bool) : (W gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih => rw [W_snoc]; simp [ih]; omega

lemma getD_snoc (l : List Bool) (v : Bool) (i : Nat) :
    (l ++ [v]).getD i false =
      if i < l.length then l.getD i false else if i = l.length then v else false := by
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2
    rw [List.getD_append_right _ _ _ _ (le_refl _)]
    simp
  · rw [List.getD_eq_default]
    simp
    omega

lemma W_input (gs : List Gate) (x : List Bool) (i : Nat) (hi : i < x.length) :
    (W gs x).getD i false = x.getD i false := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc, getD_snoc, W_length, if_pos (by omega)]
    exact ih

lemma op_mono (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or) (fX fY : Nat → Bool)
    (hx : g.op.eval (g.inputs.map fX) = true) (hy : g.op.eval (g.inputs.map fY) = false) :
    ∃ i ∈ g.inputs, fX i = true ∧ fY i = false := by
  rcases hg with h | h
  · rw [h] at hx hy
    simp only [GateOp.eval, List.all_map, List.all_eq_true, List.all_eq_false, Function.comp_apply,
      id] at hx hy
    obtain ⟨i, hi, hfy⟩ := hy
    exact ⟨i, hi, hx i hi, by simpa using hfy⟩
  · rw [h] at hx hy
    simp only [GateOp.eval, List.any_map, List.any_eq_true, List.any_eq_false, Function.comp_apply,
      id] at hx hy
    obtain ⟨i, hi, hfx⟩ := hx
    exact ⟨i, hi, hfx, by simpa using hy i hi⟩

lemma W_mono (gs : List Gate) (mono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (Z Y : List Bool) (hlen : Z.length = Y.length)
    (h : ∀ i, Z.getD i false = true → Y.getD i false = true) :
    ∀ i, (W gs Z).getD i false = true → (W gs Y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => simpa [W] using h
  | append_singleton gs g ih =>
    have ih' := ih (fun g' hg' => mono g' (List.mem_append_left _ hg'))
    have hg := mono g (by simp)
    intro i hi
    rw [W_snoc, getD_snoc, W_length] at hi ⊢
    by_cases h1 : i < Z.length + gs.length
    · rw [if_pos h1] at hi
      rw [if_pos (by omega)]
      exact ih' i hi
    · rw [if_neg h1] at hi
      rw [if_neg (by omega)]
      by_cases h2 : i = Z.length + gs.length
      · rw [if_pos h2] at hi
        rw [if_pos (by omega)]
        by_contra hne
        have hy : g.op.eval (g.inputs.map fun i => (W gs Y).getD i false) = false := by
          simpa using hne
        obtain ⟨i', _, hzi, hyi⟩ := op_mono g hg _ _ hi hy
        rw [ih' i' hzi] at hyi
        exact absurd hyi (by simp)
      · rw [if_neg h2] at hi
        exact absurd hi (by simp)

end PEqualNP.Outside.L_meta_4069

open PEqualNP.Outside.L_meta_4069 PEqualNP.CircuitLowerBounds in
theorem PEqualNP.Outside.L_meta_4069 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 → ∀ (x4 x5 : Fin x1 → Bool), (∀ (x6 : Fin x1), x4 x6 = Bool.true → x5 x6 = Bool.true) → PEqualNP.MetaComplexity.circuitFun x1 x2 x4 = Bool.true → PEqualNP.MetaComplexity.circuitFun x1 x2 x5 = Bool.true := by
  intro n C hmono x y hxy hx
  have mono' : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := fun g hg => by
    have := (hmono g hg).1
    simpa using this
  have key := W_mono C.gates mono' (List.ofFn x) (List.ofFn y) (by simp) (by
    intro i hi
    by_cases h : i < n
    · rw [List.getD_eq_getElem _ _ (by simpa using h)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact hxy _ hi
    · rw [List.getD_eq_default _ _ (by simpa using h)] at hi
      exact absurd hi (by simp)) C.output hx
  exact key
