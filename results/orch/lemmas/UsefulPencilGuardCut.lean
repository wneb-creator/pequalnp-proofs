import ExactPencilGuardCut

namespace PEqualNP.Outside.L_meta_1896_aux.UsefulPencilGuardCut

open PEqualNP.Outside.L_meta_1896_aux.GuardGeometry
open PEqualNP.Outside.L_meta_1896_aux.ExactPencilGuardCut

theorem exact_pencil_finite_family {J : Type*} [Fintype J]
    (supports : J → Finset (Fin 13))
    (separates : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : J, pencil p ⊆ supports j ∧ Disjoint N (supports j))
    (hsmall : Fintype.card J ≤ 38) : ∃ p : Fin 13, ∃ j : J, supports j = pencil p := by
  classical
  let e := Fintype.equivFin J
  let supportsFin : Fin (Fintype.card J) → Finset (Fin 13) := fun j => supports (e.symm j)
  have hsep : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : Fin (Fintype.card J), pencil p ⊆ supportsFin j ∧ Disjoint N (supportsFin j) := by
    intro p N hN hpN
    obtain ⟨j, hj, hNj⟩ := separates p N hN hpN
    exact ⟨e j, by simpa [supportsFin] using hj, by simpa [supportsFin] using hNj⟩
  obtain ⟨p, j, hj⟩ := exact_pencil_of_small supportsFin hsep hsmall
  exact ⟨p, e.symm j, hj⟩

theorem exact_pencil_in_separating_subfamily {k : ℕ}
    (supports : Fin k → Finset (Fin 13)) (U : Finset (Fin k))
    (separates : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j ∈ U, pencil p ⊆ supports j ∧ Disjoint N (supports j))
    (hsmall : k ≤ 38) : ∃ p : Fin 13, ∃ j ∈ U, supports j = pencil p := by
  classical
  have hcard : Fintype.card {j : Fin k // j ∈ U} ≤ 38 := by
    have hU : U.card ≤ k := by simpa using Finset.card_le_univ U
    simpa using le_trans hU hsmall
  have hsep : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : {j : Fin k // j ∈ U}, pencil p ⊆ supports j.val ∧ Disjoint N (supports j.val) := by
    intro p N hN hpN
    obtain ⟨j, hjU, hj, hNj⟩ := separates p N hN hpN
    exact ⟨⟨j, hjU⟩, hj, hNj⟩
  obtain ⟨p, j, hj⟩ := exact_pencil_finite_family (fun j : {j : Fin k // j ∈ U} =>
    supports j.val) hsep hcard
  exact ⟨p, j.val, j.property, hj⟩

end PEqualNP.Outside.L_meta_1896_aux.UsefulPencilGuardCut
