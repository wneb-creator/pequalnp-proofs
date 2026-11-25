
namespace PEqualNP.Outside.L_meta_2590.Semantic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def inputMap {m n : Nat} (f : Fin m → Option (Fin n)) (x : Fin n → Bool) : Fin m → Bool :=
  fun i => (f i).elim false x

def mapInitial {m n : Nat} (f : Fin m → Option (Fin n)) : State :=
  (List.ofFn fun i => (f i).elim (Sum.inl false) (fun j => Sum.inr j.val), [])

lemma mapInitial_inv {m n : Nat} (f : Fin m → Option (Fin n)) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn (inputMap f x)) (mapInitial f) := by
  refine ⟨by simp [mapInitial], ?_⟩
  intro i
  by_cases hi : i < m
  · let j : Fin m := ⟨i, hi⟩
    change ((mapInitial f).1.getD j.val (Sum.inl false)).Valid _ ∧
      ((mapInitial f).1.getD j.val (Sum.inl false)).val _ = _
    cases hj : f j with
    | none => simp [mapInitial, inputMap, hj, Stat.Valid, Stat.val, wiresFrom, j, hi] at *
    | some k => simp [mapInitial, inputMap, hj, Stat.Valid, Stat.val, wiresFrom, j, hi, k.isLt] at *
  · rw [List.getD_eq_default _ _ (by simpa [mapInitial] using Nat.le_of_not_gt hi),
        List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]
    exact ⟨trivial, rfl⟩

lemma inputMap_restriction {m n : Nat} (C : Circuit) (mono : Monotone2 C)
    (f : Fin m → Option (Fin n))
    (nonconstant : ∃ x y, circuitFun m C (inputMap f x) ≠ circuitFun m C (inputMap f y)) :
    ∃ D : Circuit, Monotone2 D ∧
      (∀ x, circuitFun n D x = circuitFun m C (inputMap f x)) ∧ D.size ≤ C.size := by
  let s := elim n C.gates (mapInitial f)
  have value (x : Fin n → Bool) :
      (stat s C.output).val (wiresFrom s.2 (List.ofFn x)) = circuitFun m C (inputMap f x) := by
    exact ((inv_elim n _ (by simp) C.gates _ _ mono (mapInitial_inv f x)).2 C.output).2
  cases hs : stat s C.output with
  | inl b =>
    obtain ⟨x, y, different⟩ := nonconstant
    have hx := value x
    have hy := value y
    rw [hs] at hx hy
    exact (different (hx.symm.trans hy)).elim
  | inr j =>
    refine ⟨⟨s.2, j⟩, elim_good n _ _ mono (by simp [mapInitial]), ?_, ?_⟩
    · intro x
      change (wiresFrom s.2 (List.ofFn x)).getD j false = _
      simpa only [hs, Stat.val] using value x
    · have size := elim_len n C.gates (mapInitial f)
      simpa only [s, mapInitial, List.length_nil, Nat.zero_add, Circuit.size] using size

end PEqualNP.Outside.L_meta_2590.Semantic
