namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

lemma plane_read1_lower (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (hao : IsAO2 (N + N) C)
    (hc : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
        z (Fin.natAdd N l) = true))
    (hr : IsReadK (N + N) C 1) : N * (q + 2) ≤ C.size + 1 := by
  classical
  obtain ⟨σ, hσ⟩ := PlaneMatching.plane_perfect_matching q N I hq hN hl hu
  have hrect : ∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
      ¬ ((p, l) ∈ incidenceEdges N I ∧ (p, l') ∈ incidenceEdges N I ∧
        (p', l) ∈ incidenceEdges N I ∧ (p', l') ∈ incidenceEdges N I) := by
    intro p p' l l' hp hl' h
    simp only [incidenceEdges, Finset.mem_filter, Finset.mem_univ, true_and] at h
    exact hp (lines_unique_intersection N I hu l l' hl' p p' h.1 h.2.1 h.2.2.1 h.2.2.2)
  have hmatch : ∀ p, (p, σ p) ∈ incidenceEdges N I := by
    intro p
    simpa only [incidenceEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hσ p
  have hcomp : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, (p, l) ∈ incidenceEdges N I ∧
        z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
    intro z
    simpa only [incidenceEdges, Finset.mem_filter, Finset.mem_univ, true_and] using hc z
  have hb := ReadOneLower.matching_bound N (incidenceEdges N I) σ C hrect hmatch hao hcomp hr
  have he : (incidenceEdges N I).card = N * (q + 1) := incidence_card N q I hl
  rw [he] at hb
  simpa only [Nat.mul_add, Nat.mul_one, Nat.mul_two, Nat.add_assoc] using hb

lemma plane_normalization_iff_gate_budget (q N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel I] (C : Circuit) (hq : 0 < q) (hN : N = q ^ 2 + q + 1)
    (hl : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hu : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (∃ D : Circuit, IsAO2 (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ IsReadK (N + N) D 1) ↔
      N * (q + 2) - 1 ≤ C.size := by
  constructor
  · rintro ⟨D, hao, hc, hsize, hr⟩
    have hb := plane_read1_lower q N I D hq hN hl hu hao hc hr
    omega
  · exact plane_normalize_of_gate_budget N q I C hl

end PEqualNP.Outside.L_meta_2583
