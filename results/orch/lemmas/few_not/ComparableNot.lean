import Mathlib.Data.Bool.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.ByContra

namespace PEqualNP.Outside.L_meta_2592_aux

lemma replace_not_false_of_output_le_operand {α : Type*}
    (f u : α → Bool) (F : α → Bool → Bool)
    (mono : ∀ x, F x false = true → F x true = true)
    (computes : ∀ x, F x (!(u x)) = f x)
    (comparable : ∀ x, f x = true → u x = true) :
    ∀ x, F x false = f x := by
  intro x
  have hm := mono x
  have hc := computes x
  have hp := comparable x
  cases hf : f x <;> cases hu : u x <;> cases hF0 : F x false <;> cases hF1 : F x true <;> simp_all

lemma replace_not_true_of_operand_le_output {α : Type*}
    (f u : α → Bool) (F : α → Bool → Bool)
    (mono : ∀ x, F x false = true → F x true = true)
    (computes : ∀ x, F x (!(u x)) = f x)
    (comparable : ∀ x, u x = true → f x = true) :
    ∀ x, F x true = f x := by
  intro x
  have hm := mono x
  have hc := computes x
  have hp := comparable x
  cases hf : f x <;> cases hu : u x <;> cases hF0 : F x false <;> cases hF1 : F x true <;> simp_all

lemma essential_not_incomparable {α : Type*}
    (f u : α → Bool) (F : α → Bool → Bool)
    (mono : ∀ x, F x false = true → F x true = true)
    (computes : ∀ x, F x (!(u x)) = f x)
    (falseChanges : ∃ x, F x false ≠ f x)
    (trueChanges : ∃ x, F x true ≠ f x) :
    (∃ x, f x = true ∧ u x = false) ∧
    (∃ x, u x = true ∧ f x = false) := by
  obtain ⟨a, ha⟩ := falseChanges
  obtain ⟨b, hb⟩ := trueChanges
  constructor
  · refine ⟨a, ?_⟩
    have hm := mono a
    have hc := computes a
    cases hf : f a <;> cases hu : u a <;> cases hF0 : F a false <;> cases hF1 : F a true <;> simp_all
  · refine ⟨b, ?_⟩
    have hm := mono b
    have hc := computes b
    cases hf : f b <;> cases hu : u b <;> cases hF0 : F b false <;> cases hF1 : F b true <;> simp_all

lemma all_edges_force_operand {n : ℕ}
    (edges : List (Fin n × Fin n)) (u : (Fin n → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
    (onEdges : ∀ e ∈ edges, u (fun i => decide (i = e.1 ∨ i = e.2)) = true) :
    ∀ x, edges.any (fun e => x e.1 && x e.2) = true → u x = true := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := List.any_eq_true.mp hx
  obtain ⟨hleft, hright⟩ := Bool.and_eq_true_iff.mp hxe
  apply mono _ x ?_ (onEdges e he)
  intro i hi
  have hi' : i = e.1 ∨ i = e.2 := by simpa using hi
  rcases hi' with h | h
  · simpa [h] using hleft
  · simpa [h] using hright

lemma essential_not_has_false_edge {n : ℕ}
    (edges : List (Fin n × Fin n)) (u : (Fin n → Bool) → Bool)
    (F : (Fin n → Bool) → Bool → Bool)
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
    (suffixMono : ∀ x, F x false = true → F x true = true)
    (computes : ∀ x, F x (!(u x)) = edges.any (fun e => x e.1 && x e.2))
    (falseChanges : ∃ x, F x false ≠ edges.any (fun e => x e.1 && x e.2)) :
    ∃ e ∈ edges, u (fun i => decide (i = e.1 ∨ i = e.2)) = false := by
  classical
  by_contra! noEdge
  have onEdges : ∀ e ∈ edges,
      u (fun i => decide (i = e.1 ∨ i = e.2)) = true := by
    intro e he
    have h := noEdge e he
    cases hu : u (fun i => decide (i = e.1 ∨ i = e.2)) <;> simp_all
  have replacement := replace_not_false_of_output_le_operand
    (fun x => edges.any (fun e => x e.1 && x e.2)) u F suffixMono computes
    (all_edges_force_operand edges u operandMono onEdges)
  obtain ⟨x, hx⟩ := falseChanges
  exact hx (replacement x)

lemma essential_not_has_true_independent {n : ℕ}
    (f u : (Fin n → Bool) → Bool) (F : (Fin n → Bool) → Bool → Bool)
    (tests : List (Fin n → Bool))
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
    (suffixMono : ∀ x, F x false = true → F x true = true)
    (computes : ∀ x, F x (!(u x)) = f x)
    (cover : ∀ x, f x = false → ∃ y ∈ tests, ∀ i, x i = true → y i = true)
    (trueChanges : ∃ x, F x true ≠ f x) :
    ∃ y ∈ tests, u y = true := by
  obtain ⟨x, hx⟩ := trueChanges
  have witness : u x = true ∧ f x = false := by
    have hm := suffixMono x
    have hc := computes x
    cases hf : f x <;> cases hu : u x <;> cases hF0 : F x false <;> cases hF1 : F x true <;> simp_all
  obtain ⟨y, hy, hxy⟩ := cover x witness.2
  exact ⟨y, hy, operandMono x y hxy witness.1⟩

lemma monotone_operand_endpoints {n : ℕ} (u : (Fin n → Bool) → Bool)
    (mono : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
    (takesFalse : ∃ x, u x = false) (takesTrue : ∃ x, u x = true) :
    u (fun _ => false) = false ∧ u (fun _ => true) = true := by
  obtain ⟨x, hx⟩ := takesFalse
  obtain ⟨y, hy⟩ := takesTrue
  constructor
  · cases hzero : u (fun _ => false)
    · rfl
    · have hbad := mono (fun _ => false) x (by simp) hzero
      simp_all
  · exact mono y (fun _ => true) (by simp) hy

lemma proper_output_not_negation {n : ℕ}
    (f u : (Fin n → Bool) → Bool)
    (operandMono : ∀ x y, (∀ i, x i = true → y i = true) → u x = true → u y = true)
    (zero : f (fun _ => false) = false)
    (one : f (fun _ => true) = true) :
    ¬ ∀ x, !(u x) = f x := by
  intro computes
  have hc0 := computes (fun _ => false)
  have hc1 := computes (fun _ => true)
  have hm := operandMono (fun _ => false) (fun _ => true) (by simp)
  cases hu0 : u (fun _ => false) <;> cases hu1 : u (fun _ => true) <;> simp_all

lemma proper_output_not_and_not {n : ℕ}
    (f u a : (Fin n → Bool) → Bool)
    (operandOne : u (fun _ => true) = true)
    (outputOne : f (fun _ => true) = true) :
    ¬ ∀ x, (a x && !(u x)) = f x := by
  intro computes
  have h := computes (fun _ => true)
  simp_all

lemma proper_output_not_or_not {n : ℕ}
    (f u a : (Fin n → Bool) → Bool)
    (operandZero : u (fun _ => false) = false)
    (outputZero : f (fun _ => false) = false) :
    ¬ ∀ x, (a x || !(u x)) = f x := by
  intro computes
  have h := computes (fun _ => false)
  simp_all

end PEqualNP.Outside.L_meta_2592_aux
