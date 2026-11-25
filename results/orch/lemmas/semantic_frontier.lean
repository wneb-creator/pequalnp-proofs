import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux.SemanticFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma prime_below {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = true) :
    ∃ S : Finset (Fin n), IsPrimeImplicant n C S ∧
      ∀ i ∈ S, x i = true := by
  classical
  let X : Finset (Fin n) := Finset.univ.filter fun i => x i = true
  have hX : setInput X = x := by
    funext i
    cases hi : x i <;> simp [setInput, X, hi]
  have hex : ∃ k : ℕ, ∃ S : Finset (Fin n),
      S ⊆ X ∧ circuitFun n C (setInput S) = true ∧ S.card = k :=
    ⟨X.card, X, Finset.Subset.refl _, by simpa [hX] using hx, rfl⟩
  obtain ⟨S, hSX, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, ⟨hS, ?_⟩, ?_⟩
  · intro T hT
    have hproper : T ⊂ S := Finset.mem_ssubsets.mp hT
    by_contra hfalse
    have htrue : circuitFun n C (setInput T) = true := by
      cases h : circuitFun n C (setInput T) <;> simp_all
    have hmin : Nat.find hex ≤ T.card :=
      Nat.find_min' hex ⟨T, hproper.1.trans hSX, htrue, rfl⟩
    have hlt := Finset.card_lt_card hproper
    omega
  · intro i hi
    exact (Finset.mem_filter.mp (hSX hi)).2

lemma lower_agrees_on_primes {n : ℕ} (C : Circuit)
    (f : (Fin n → Bool) → Bool) (hmono : Monotone f)
    (hle : ∀ x, f x ≤ circuitFun n C x)
    (hprime : ∀ S, IsPrimeImplicant n C S → f (setInput S) = true) :
    f = circuitFun n C := by
  funext x
  apply le_antisymm (hle x)
  by_cases hx : circuitFun n C x = true
  · obtain ⟨S, hS, hsub⟩ := prime_below C x hx
    have hi : setInput S ≤ x := by
      intro i
      by_cases hmem : i ∈ S
      · simp [setInput, hmem, hsub i hmem]
      · simp [setInput, hmem]
    have h := hmono hi
    simpa only [hprime S hS, hx] using h
  · have hfalse : circuitFun n C x = false := by
      cases h : circuitFun n C x <;> simp_all
    rw [hfalse]
    exact bot_le

end PEqualNP.Outside.L_meta_2583_aux.SemanticFrontier
