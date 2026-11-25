import SurplusCover
import BipartiteGeometry
import DegreeTwoCard

namespace PEqualNP.Outside.L_meta_4675_aux.CycleClass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2590_aux.Surplus
open PEqualNP.Outside.L_meta_4970_aux

lemma vertex_cover_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hdegree : ∀ v, 2 ≤ (neighbours E v).card)
    (hAO : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hcompute : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      (p + l) + S.card ≤ C.size + 1 := by
  by_cases hn : 0 < p + l
  · have hmono : Monotone2 C := by
      intro g hg
      refine ⟨?_, (hAO.2.2 g hg).le⟩
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hAO.1 g hg
    have hc : ∀ x : Fin (p + l) → Bool,
        C.eval (List.ofFn x) = true ↔ sem_Edge (BipartiteGeometry.Adj E) x := by
      intro x
      change circuitFun (p + l) C x = true ↔ _
      rw [hcompute x]
      simp only [decide_eq_true_eq]
      exact (BipartiteGeometry.edge_iff E x).symm
    obtain ⟨S, hS, hsize⟩ := SurplusCover.circuit_cover hn (BipartiteGeometry.Adj E)
      (BipartiteGeometry.sem_geometry E hfour hdegree) C hmono hc
    refine ⟨S, ?_, hsize⟩
    intro a b hab
    apply hS (Fin.castAdd l a) (Fin.natAdd p b)
    change Fin.natAdd p b ∈ neighbours E (Fin.castAdd l a)
    rw [neighbours_left]
    exact Finset.mem_image.mpr ⟨b, by simp [hab], rfl⟩
  · have hp : p = 0 := by omega
    have hl : l = 0 := by omega
    subst p l
    refine ⟨∅, ?_, by simp⟩
    intro a
    exact Fin.elim0 a

lemma degree_two_bound (p l : ℕ) (E : Finset (Fin p × Fin l)) (C : Circuit)
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (hdegree : ∀ v, (neighbours E v).card = 2)
    (hAO : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hcompute : ∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x =
      decide (∃ (a : Fin p) (b : Fin l), (a, b) ∈ E ∧
        x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true)) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  obtain ⟨S, hS, hsize⟩ := vertex_cover_bound p l E C hfour (fun v => (hdegree v).ge) hAO hcompute
  exact ⟨S, hS, by rw [DegreeTwoCard.edges_eq_vertices E hdegree]; exact hsize⟩

end PEqualNP.Outside.L_meta_4675_aux.CycleClass
