import PEqualNP.Defs.AndCountCircuit

theorem PEqualNP.Outside.L_meta_949_aux.existingCutCounterexample :
    ¬ (∀ (G : SimpleGraph (Fin 6)) (C : PEqualNP.AndCount.AndCountCircuit 6),
      C.WellFormed →
      (∀ I : Finset (Fin 6),
        (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) →
        (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v) →
        C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true) →
      ¬ (∃ (k : ℕ) (X Y : Fin k → Finset (Fin 6)),
        k ≤ C.size ∧
        (∀ i : Fin k, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
        (∀ a b : Fin 6, G.Adj a b → ∃ i : Fin k,
          (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)))) := by
  intro h
  apply h (⊥ : SimpleGraph (Fin 6))
    (PEqualNP.AndCount.AndCountCircuit.starCircuit (⊥ : SimpleGraph (Fin 6)) ∅)
  · simp [PEqualNP.AndCount.AndCountCircuit.WellFormed,
      PEqualNP.AndCount.AndCountCircuit.starCircuit]
  · intro I _ hmax
    constructor
    · simp [PEqualNP.AndCount.AndCountCircuit.eval,
        PEqualNP.AndCount.AndCountCircuit.starCircuit]
    · intro u hu
      obtain ⟨v, _, hv⟩ := hmax u hu
      exact False.elim hv
  · refine ⟨0, fun _ => ∅, fun _ => ∅, Nat.zero_le _, ?_, ?_⟩
    · intro i
      exact Fin.elim0 i
    · intro a b hab
      exact False.elim hab
