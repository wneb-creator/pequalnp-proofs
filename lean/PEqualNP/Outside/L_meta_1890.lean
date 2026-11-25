import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def seed (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) : List Bool :=
  List.ofFn (x ∘ p) ++ [x 0 && x 2]

def neighbor : Fin 10 → Fin 10 := ![1, 0, 1, 2, 3, 0, 1, 2, 3, 4]

def singleton (v : Fin 10) (i : Fin 10) : Bool := i == v

def pair (v : Fin 10) (i : Fin 10) : Bool := (i == v) || (i == neighbor v)

lemma witnesses : ∀ v : Fin 10,
    edge (singleton (neighbor v)) = false ∧ edge (pair v) = true ∧
    (singleton (neighbor v) 0 && singleton (neighbor v) 2) = false ∧
    (pair v 0 && pair v 2) = false := by
  decide +kernel

lemma missing_counterexample (C : PEqualNP.CircuitLowerBounds.Circuit)
    (p : Fin 10 → Fin 10) (v : Fin 10) (hv : ∀ i, p i ≠ v) :
    ∃ x : Fin 10 → Bool, C.eval (seed p x) ≠ edge x := by
  have hm : singleton (neighbor v) ∘ p = pair v ∘ p := by
    funext i
    simp [Function.comp_def, singleton, pair, hv i]
  have hs : seed p (singleton (neighbor v)) = seed p (pair v) := by
    simp only [seed, hm, (witnesses v).2.2.1, (witnesses v).2.2.2]
  by_cases h : C.eval (seed p (singleton (neighbor v))) = edge (singleton (neighbor v))
  · refine ⟨pair v, ?_⟩
    rw [← hs, h, (witnesses v).1, (witnesses v).2.1]
    decide
  · exact ⟨singleton (neighbor v), h⟩

lemma computes_surjective (C : PEqualNP.CircuitLowerBounds.Circuit)
    (p : Fin 10 → Fin 10) (h : ∀ x, C.eval (seed p x) = edge x) :
    Function.Surjective p := by
  classical
  intro v
  by_contra hv
  have missing : ∀ i, p i ≠ v := fun i hi => hv ⟨i, hi⟩
  obtain ⟨x, hx⟩ := missing_counterexample C p v missing
  exact hx (h x)

end PEqualNP.Outside.L_meta_1890
