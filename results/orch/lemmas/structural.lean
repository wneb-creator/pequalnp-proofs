import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor (i : Fin 10) : Fin 10 :=
  ![1, 2, 3, 4, 0, 7, 8, 9, 5, 6] i

def singletonInput (i : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = neighbor i)

def edgeInput (i : Fin 10) : Fin 10 → Bool :=
  fun j => decide (j = i ∨ j = neighbor i)

lemma singleton_target (i : Fin 10) : target (singletonInput i) = false := by
  fin_cases i <;> decide

lemma edge_target (i : Fin 10) : target (edgeInput i) = true := by
  fin_cases i <;> decide

lemma inputs_agree (i j : Fin 10) (h : j ≠ i) :
    singletonInput i j = edgeInput i j := by
  simp [singletonInput, edgeInput, h]

lemma omitted_vertex
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (i : Fin 10) (omitted : ∀ j, σ j ≠ i)
    (sameFree : u (singletonInput i 0) = u (edgeInput i 0)) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  have same :
      List.ofFn (singletonInput i ∘ σ) ++ [u (singletonInput i 0)] =
      List.ofFn (edgeInput i ∘ σ) ++ [u (edgeInput i 0)] := by
    have hfirst : singletonInput i ∘ σ = edgeInput i ∘ σ := by
      funext j
      exact inputs_agree i (σ j) (omitted j)
    rw [hfirst, sameFree]
  by_cases h : C.eval (List.ofFn (singletonInput i ∘ σ) ++
      [u (singletonInput i 0)]) = false
  · refine ⟨edgeInput i, ?_⟩
    rw [edge_target, ← same, h]
    decide
  · refine ⟨singletonInput i, ?_⟩
    rwa [singleton_target]

lemma omitted_nonzero_vertex
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (i : Fin 10) (hi : i ≠ 0)
    (omitted : ∀ j, σ j ≠ i) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  apply omitted_vertex C σ u i omitted
  rw [inputs_agree i 0 (Ne.symm hi)]

lemma omitted_vertex_constant_free
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (i : Fin 10) (constant : u false = u true)
    (omitted : ∀ j, σ j ≠ i) :
    ∃ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) ≠ target x := by
  apply omitted_vertex C σ u i omitted
  have same (a b : Bool) : u a = u b := by
    cases a <;> cases b <;> simp [constant]
  exact same _ _

lemma necessary_vertex_coverage
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = target x) :
    ∀ i : Fin 10, i ≠ 0 → ∃ j, σ j = i := by
  intro i hi
  by_contra omitted
  push Not at omitted
  obtain ⟨x, different⟩ := omitted_nonzero_vertex C σ u i hi omitted
  exact different (computes x)

lemma necessary_coverage_or_nonconstant
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = target x) :
    Function.Surjective σ ∨ u false ≠ u true := by
  by_cases constant : u false = u true
  · left
    intro i
    by_contra omitted
    push Not at omitted
    obtain ⟨x, different⟩ := omitted_vertex_constant_free C σ u i constant omitted
    exact different (computes x)
  · exact Or.inr constant

lemma free_nonconstant_of_omitted_zero
    (C : PEqualNP.CircuitLowerBounds.Circuit) (σ : Fin 10 → Fin 10)
    (u : Bool → Bool) (omitted : ∀ j, σ j ≠ 0)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)]) = target x) :
    u false ≠ u true := by
  intro constant
  obtain ⟨x, different⟩ := omitted_vertex_constant_free C σ u 0 constant omitted
  exact different (computes x)

lemma unary_nonconstant_cases (u : Bool → Bool) (h : u false ≠ u true) :
    u = id ∨ u = Bool.not := by
  cases hf : u false <;> cases ht : u true
  · exact False.elim (h (hf.trans ht.symm))
  · left
    funext b
    cases b <;> simp [hf, ht]
  · right
    funext b
    cases b <;> simp [hf, ht]
  · exact False.elim (h (hf.trans ht.symm))

lemma target_separation (q : Fin 10) :
    ∃ x y : Fin 10 → Bool, x q = y q ∧ x 0 = y 0 ∧ target x ≠ target y := by
  have choice : ∃ i : Fin 10, i ≠ q ∧ i ≠ 0 := by
    by_cases hq : q = 1
    · exact ⟨2, by omega, by decide⟩
    · exact ⟨1, Ne.symm hq, by decide⟩
  obtain ⟨i, hiq, hi0⟩ := choice
  refine ⟨singletonInput i, edgeInput i,
    inputs_agree i q (Ne.symm hiq), inputs_agree i 0 (Ne.symm hi0), ?_⟩
  rw [singleton_target, edge_target]
  decide

end PEqualNP.Outside.L_meta_1884
