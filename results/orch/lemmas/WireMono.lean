import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.WireMono
    {n : ℕ} (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool)
    (hxy : ∀ j, x j = true → y j = true) (i : ℕ) :
    (C.wires (List.ofFn x)).getD i false = true →
      (C.wires (List.ofFn y)).getD i false = true := by
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]
  let Le := fun (w z : List Bool) =>
    ∀ j : ℕ, w.getD j false = true → z.getD j false = true
  have extend (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w z : List Bool)
      (len : w.length = z.length) (le : Le w z) :
      Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g)
        (by simp [step, len])
      have gate : g.op.eval (g.inputs.map fun j => w.getD j false) = true →
          g.op.eval (g.inputs.map fun j => z.getD j false) = true := by
        rcases ok g (by simp) with hop | hop
        · rw [hop]
          change (g.inputs.map fun j => w.getD j false).all id = true →
            (g.inputs.map fun j => z.getD j false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h j hj
          exact le j (h j hj)
        · rw [hop]
          change (g.inputs.map fun j => w.getD j false).any id = true →
            (g.inputs.map fun j => z.getD j false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨j, hj, ha⟩
          exact ⟨j, hj, le j ha⟩
      intro j
      by_cases small : j < w.length
      · simpa only [step, List.getD_append _ _ _ _ small,
          List.getD_append _ _ _ _ (len ▸ small)] using le j
      · have big : w.length ≤ j := by omega
        simp only [step, List.getD_append_right _ _ _ _ big,
          List.getD_append_right _ _ _ _ (len ▸ big), ← len]
        cases e : j - w.length with
        | zero => exact gate
        | succ k => simp
  have init : Le (List.ofFn x) (List.ofFn y) := by
    intro j
    by_cases hj : j < n
    · rw [List.getD_eq_getElem (List.ofFn x) false
            (by simpa only [List.length_ofFn] using hj),
          List.getD_eq_getElem (List.ofFn y) false
            (by simpa only [List.length_ofFn] using hj)]
      simp only [List.getElem_ofFn]
      exact hxy ⟨j, hj⟩
    · rw [List.getD_eq_default (List.ofFn x) false
            (by simp only [List.length_ofFn]; omega)]
      intro h
      exact Bool.noConfusion h
  exact extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp) init i
