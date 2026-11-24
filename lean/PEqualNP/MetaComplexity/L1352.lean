import PEqualNP.Defs

theorem PEqualNP.MetaComplexity.L1352 : ∀ p : Fin 7, ∃ σ τ : Equiv.Perm (Fin 7), σ p = 6 ∧ ∀ i : Fin 7, (((![{0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {0, 4, 5}, {1, 5, 6}, {0, 2, 6}] : Fin 7 → Finset (Fin 7)) i).erase p).map σ.toEmbedding = ((![{0, 2}, {3, 4}, {1, 5}, {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {0, 4, 5}] : Fin 7 → Finset (Fin 6)) (τ i)).map Fin.castSuccEmb := by
  intro p
  fin_cases p
  · exact ⟨Equiv.ofBijective (![6, 0, 1, 2, 3, 4, 5] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![0, 3, 4, 5, 1, 6, 2] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
  · exact ⟨Equiv.ofBijective (![0, 6, 1, 2, 5, 4, 3] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![0, 2, 4, 5, 6, 1, 3] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
  · exact ⟨Equiv.ofBijective (![0, 1, 6, 3, 5, 4, 2] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![3, 2, 1, 5, 6, 4, 0] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
  · exact ⟨Equiv.ofBijective (![0, 2, 1, 6, 4, 5, 3] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![0, 4, 2, 1, 6, 5, 3] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
  · exact ⟨Equiv.ofBijective (![0, 1, 5, 3, 6, 2, 4] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![3, 2, 5, 1, 0, 4, 6] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
  · exact ⟨Equiv.ofBijective (![0, 1, 4, 3, 2, 6, 5] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![3, 4, 1, 5, 0, 2, 6] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
  · exact ⟨Equiv.ofBijective (![0, 1, 2, 3, 4, 5, 6] : Fin 7 → Fin 7) (by decide), Equiv.ofBijective (![3, 4, 5, 1, 6, 2, 0] : Fin 7 → Fin 7) (by decide), by decide, by decide⟩
