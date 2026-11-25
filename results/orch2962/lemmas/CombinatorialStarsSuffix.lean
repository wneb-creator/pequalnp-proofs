
namespace PEqualNP.Outside.L_meta_2962_aux.Combinatorial

open PEqualNP.MetaComplexity.NestedCover

variable {n : ℕ} (G : SimpleGraph (Fin n))

theorem star_cover (D : Finset (Sym2 (Fin n))) (S L : Finset (Fin n))
    (f : Fin n → Fin n) (hD : D = L.image (fun v => s(f v, v)))
    (hf : ∀ v ∈ L, f v ∈ S) : CoversDeleted G D S := by
  intro u v _ huv
  rw [hD] at huv
  obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp huv
  rcases Sym2.eq_iff.mp heq with h | h
  · exact Or.inl (h.1 ▸ hf w hw)
  · exact Or.inr (h.1 ▸ hf w hw)

theorem star_vertices_incident (D : Finset (Sym2 (Fin n))) (S L : Finset (Fin n))
    (f : Fin n → Fin n) (hD : D = L.image (fun v => s(f v, v)))
    (hS : S ⊆ L.image f) :
    ∀ v ∈ S ∪ L, ∃ e ∈ D, v ∈ e := by
  intro v hv
  rcases Finset.mem_union.mp hv with h | h
  · obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp (hS h)
    refine ⟨s(f w, w), ?_, ?_⟩
    · rw [hD]
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    · rw [← heq]
      exact Sym2.mem_mk_left _ _
  · refine ⟨s(f v, v), ?_, Sym2.mem_mk_right _ _⟩
    rw [hD]
    exact Finset.mem_image.mpr ⟨v, h, rfl⟩

theorem star_forest_budget_sufficient (D : Finset (Sym2 (Fin n)))
    (S L T R : Finset (Fin n)) (f : Fin n → Fin n) (budget : ℕ)
    (hD : D = L.image (fun v => s(f v, v)))
    (hf : ∀ v ∈ L, f v ∈ S) (hdisj : Disjoint S L)
    (hvertices : (S ∪ L).card ≤ budget)
    (hT : IsMinCover G T)
    (hR : (G.deleteEdges (D : Set (Sym2 (Fin n)))).IsVertexCover
      (R : Set (Fin n))) : D.card + T.card ≤ budget + R.card := by
  have hcard : D.card ≤ L.card := by
    rw [hD]
    exact Finset.card_image_le
  have hsum := Finset.card_union_of_disjoint hdisj
  apply core_budget_sufficient G D T R S budget hT hR (star_cover G D S L f hD hf)
  omega

end PEqualNP.Outside.L_meta_2962_aux.Combinatorial
