import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (v : Fin 10) : Fin 10 :=
  match v.val with
  | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 4 | 4 => 0
  | 5 => 7 | 6 => 8 | 7 => 9 | 8 => 5 | _ => 6

def witness0 (v : Fin 10) : Fin 10 → Bool := fun i => decide (i = neighbor v)

def witness1 (v : Fin 10) : Fin 10 → Bool := fun i => decide (i = v ∨ i = neighbor v)

lemma witness_agree (v i : Fin 10) (h : i ≠ v) : witness0 v i = witness1 v i := by
  simp [witness0, witness1, h]

lemma witness_seed : ∀ v : Fin 10,
    (witness0 v 0 && witness0 v 2) = (witness1 v 0 && witness1 v 2) := by
  decide

lemma witness_target : ∀ v : Fin 10, target (witness0 v) = false ∧ target (witness1 v) = true := by
  decide

lemma inputMap_surjective (σ : Fin 10 → Fin 10) (F : List Bool → Bool)
    (h : ∀ x : Fin 10 → Bool,
      F (List.ofFn (x ∘ σ) ++ [x 0 && x 2]) = target x) : Function.Surjective σ := by
  classical
  intro v
  apply Classical.byContradiction
  intro hn
  have hσ : ∀ i, σ i ≠ v := fun i hi => hn ⟨i, hi⟩
  have he : witness0 v ∘ σ = witness1 v ∘ σ := by
    funext i
    exact witness_agree v (σ i) (hσ i)
  have heinput :
      List.ofFn (witness0 v ∘ σ) ++ [witness0 v 0 && witness0 v 2] =
      List.ofFn (witness1 v ∘ σ) ++ [witness1 v 0 && witness1 v 2] := by
    rw [he, witness_seed]
  have hc := congrArg F heinput
  rw [h, h] at hc
  have hw := witness_target v
  rw [hw.1, hw.2] at hc
  cases hc

lemma nonSurjective_counterinput (σ : Fin 10 → Fin 10) (F : List Bool → Bool)
    (hσ : ¬ Function.Surjective σ) :
    ∃ x : Fin 10 → Bool, F (List.ofFn (x ∘ σ) ++ [x 0 && x 2]) ≠ target x := by
  apply Classical.byContradiction
  intro h
  apply hσ
  apply inputMap_surjective σ F
  intro x
  apply Classical.byContradiction
  intro hx
  exact h ⟨x, hx⟩

end PEqualNP.Outside.L_meta_1890
