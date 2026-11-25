import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.SemanticFrontierDual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma maximal_false_above {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = false) :
    ∃ T : Finset (Fin n), x ≤ setInput T ∧
      circuitFun n C (setInput T) = false ∧
      ∀ U : Finset (Fin n), T ⊂ U → circuitFun n C (setInput U) = true := by
  classical
  let X : Finset (Fin n) := Finset.univ.filter fun i => x i = true
  have hX : setInput X = x := by
    funext i
    cases hi : x i <;> simp [setInput, X, hi]
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin n),
      X ⊆ T ∧ circuitFun n C (setInput T) = false ∧ n - T.card = k :=
    ⟨n - X.card, X, Finset.Subset.refl _, by simpa [hX] using hx, rfl⟩
  obtain ⟨T, hXT, hT, hcard⟩ := Nat.find_spec hex
  refine ⟨T, ?_, hT, ?_⟩
  · intro i
    by_cases hi : x i = true
    · have hmem : i ∈ T := hXT (by simp [X, hi])
      simp [setInput, hmem, hi]
    · have hfalse : x i = false := by cases h : x i <;> simp_all
      simp [hfalse]
  · intro U hproper
    by_contra htrue
    have hfalse : circuitFun n C (setInput U) = false := by
      cases h : circuitFun n C (setInput U) <;> simp_all
    have hmin : Nat.find hex ≤ n - U.card :=
      Nat.find_min' hex ⟨U, hXT.trans hproper.1, hfalse, rfl⟩
    have hlt := Finset.card_lt_card hproper
    have hbound : U.card ≤ n := by simpa using Finset.card_le_univ U
    omega

lemma upper_agrees_on_maximal_false {n : ℕ} (C : Circuit)
    (f : (Fin n → Bool) → Bool) (hmono : Monotone f)
    (hle : ∀ x, circuitFun n C x ≤ f x)
    (hmax : ∀ T : Finset (Fin n), circuitFun n C (setInput T) = false →
      (∀ U : Finset (Fin n), T ⊂ U → circuitFun n C (setInput U) = true) →
      f (setInput T) = false) :
    f = circuitFun n C := by
  funext x
  apply le_antisymm ?_ (hle x)
  by_cases hx : circuitFun n C x = false
  · obtain ⟨T, hsub, hT, hU⟩ := maximal_false_above C x hx
    have h := hmono hsub
    simpa only [hmax T hT hU, hx] using h
  · have htrue : circuitFun n C x = true := by
      cases h : circuitFun n C x <;> simp_all
    rw [htrue]
    exact le_top

end PEqualNP.Outside.L_meta_2583_aux.SemanticFrontierDual
