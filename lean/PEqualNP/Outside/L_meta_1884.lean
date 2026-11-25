import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.InputEssentiality

open PEqualNP.CircuitLowerBounds

def target (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def neighbor : Fin 10 → Fin 10 := ![1, 2, 3, 4, 0, 0, 1, 2, 3, 4]

def singleton (v : Fin 10) : Fin 10 → Bool := fun j => decide (j = v)

def pair (v w : Fin 10) : Fin 10 → Bool := fun j => decide (j = v ∨ j = w)

lemma singleton_false : ∀ v : Fin 10, target (singleton v) = false := by decide

lemma neighbor_pair_true : ∀ v : Fin 10, target (pair v (neighbor v)) = true := by
  decide

lemma map_covers_nonzero (C : Circuit) (π : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcomputes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) = target x) :
    ∀ v : Fin 10, v ≠ 0 → ∃ i : Fin 10, π i = v := by
  classical
  intro v hv
  by_contra hmissing
  have hn : ∀ i, π i ≠ v := by simpa only [not_exists] using hmissing
  have hzero : (0 : Fin 10) ≠ v := Ne.symm hv
  have hcomp : pair v (neighbor v) ∘ π = singleton (neighbor v) ∘ π := by
    funext i
    simp [Function.comp_def, pair, singleton, hn i]
  have harg :
      List.ofFn (pair v (neighbor v) ∘ π) ++ [u (pair v (neighbor v) 0)] =
      List.ofFn (singleton (neighbor v) ∘ π) ++ [u (singleton (neighbor v) 0)] := by
    rw [hcomp]
    simp [pair, singleton, hzero]
  have heq := congrArg C.eval harg
  rw [hcomputes, hcomputes, neighbor_pair_true, singleton_false] at heq
  cases heq

lemma missing_nonzero_counterexample (C : Circuit) (π : Fin 10 → Fin 10)
    (u : Bool → Bool) (v : Fin 10) (hv : v ≠ 0) (hmissing : ∀ i, π i ≠ v) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) ≠ target x := by
  classical
  by_contra h
  have hcomputes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) = target x := by
    simpa only [not_exists, not_not] using h
  obtain ⟨i, hi⟩ := map_covers_nonzero C π u hcomputes v hv
  exact hmissing i hi

lemma map_surjective_of_zero (C : Circuit) (π : Fin 10 → Fin 10) (u : Bool → Bool)
    (hcomputes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ π) ++ [u (x 0)]) = target x)
    (hzero : ∃ i : Fin 10, π i = 0) : Function.Surjective π := by
  intro v
  by_cases hv : v = 0
  · simpa only [hv] using hzero
  · exact map_covers_nonzero C π u hcomputes v hv

end PEqualNP.Outside.L_meta_1884.InputEssentiality
