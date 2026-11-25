import RestrictedUnionBound

namespace PEqualNP.Outside.L_meta_1896_aux.ExactPencilGuardCut

open PEqualNP.Outside.L_meta_1896_aux.GuardGeometry
open PEqualNP.Outside.L_meta_1896_aux.GuardCharging
open PEqualNP.Outside.L_meta_1896_aux.RestrictedUnionBound

theorem no_exact_pencil_bound {k : ℕ} (supports : Fin k → Finset (Fin 13))
    (separates : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : Fin k, pencil p ⊆ supports j ∧ Disjoint N (supports j))
    (hnone : ∀ p : Fin 13, ¬∃ j : Fin k, supports j = pencil p) : 39 ≤ k := by
  have hactive : active supports = Finset.univ := by
    ext p
    simp [active_mem, hnone p]
  have h := three_per_active_target (active supports) (guards supports) (targets supports)
    (guard_targets_card supports) (local_guard_charge supports separates)
  have hcard : (guards supports).card ≤ k := by
    simpa using Finset.card_le_univ (guards supports)
  rw [hactive] at h
  simp only [Finset.card_univ, Fintype.card_fin] at h
  omega

theorem exact_pencil_of_small {k : ℕ} (supports : Fin k → Finset (Fin 13))
    (separates : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : Fin k, pencil p ⊆ supports j ∧ Disjoint N (supports j))
    (hsmall : k ≤ 38) : ∃ p : Fin 13, ∃ j : Fin k, supports j = pencil p := by
  by_contra h
  have hnone : ∀ p : Fin 13, ¬∃ j : Fin k, supports j = pencil p := by
    intro p hp
    exact h ⟨p, hp⟩
  have hbound := no_exact_pencil_bound supports separates hnone
  omega

end PEqualNP.Outside.L_meta_1896_aux.ExactPencilGuardCut
