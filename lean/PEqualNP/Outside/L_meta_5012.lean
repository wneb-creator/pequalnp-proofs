import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.OneFlagReview

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma common_neighbors_unique {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {a b u v : Fin n}
    (hab : a ≠ b) (hau : G.Adj a u) (hbu : G.Adj b u)
    (hav : G.Adj a v) (hbv : G.Adj b v) : u = v := by
  by_contra huv
  have hlarge : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card := by
    apply Finset.one_lt_card.mpr
    exact ⟨u, by simp [hau, hbu], v, by simp [hav, hbv], huv⟩
  have hsmall := h4 a b hab
  omega

lemma no_common_neighbor_of_partial_star {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (A : Finset (Fin n))
    {ug uh vh : Fin n} (hgu : ug ≠ uh) (hgA : ug ∈ A) (hhA : uh ∈ A)
    (hgv : G.Adj ug vh) (hhv : G.Adj uh vh)
    (hmissing : ∃ a ∈ A, ¬ G.Adj a vh) :
    ¬ ∃ w : Fin n, ∀ a ∈ A, G.Adj a w := by
  rintro ⟨w, hw⟩
  have hweq := common_neighbors_unique h4 hgu hgv hhv (hw ug hgA) (hw uh hhA)
  obtain ⟨a, ha, hna⟩ := hmissing
  exact hna (hweq ▸ hw a ha)

lemma exists_mem_ne_of_two_le_card {α : Type} [DecidableEq α] (A : Finset α)
    (hA : 2 ≤ A.card) (u : α) : ∃ a ∈ A, a ≠ u := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  by_cases hau : a = u
  · exact ⟨b, hb, fun hbu => hab (hau.trans hbu.symm)⟩
  · exact ⟨a, ha, hau⟩

lemma cross_star_independent_triple {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (C D : Finset (Fin n))
    (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) {ug uh vh : Fin n}
    (hvhD : vh ∈ D) (hgu : ug ≠ uh) (hgv : G.Adj ug vh)
    (hUhD : ∀ d ∈ D, G.Adj uh d) (hCVh : ∀ c ∈ C, G.Adj c vh)
    (hUgC : ∀ c ∈ C, ¬ G.Adj ug c) :
    ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj ug c ∧ ¬ G.Adj ug d ∧ ¬ G.Adj c d := by
  obtain ⟨c, hc, hcuh⟩ := exists_mem_ne_of_two_le_card C hC uh
  obtain ⟨d, hd, hdvh⟩ := exists_mem_ne_of_two_le_card D hD vh
  refine ⟨c, hc, d, hd, hUgC c hc, ?_, ?_⟩
  · intro hugd
    have h := common_neighbors_unique h4 hgu hgv (hUhD vh hvhD) hugd (hUhD d hd)
    exact hdvh h.symm
  · intro hcd
    have h := common_neighbors_unique h4 hcuh (hCVh c hc) (hUhD vh hvhD) hcd (hUhD d hd)
    exact hdvh h.symm

lemma triple_input_graphFun_false {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {u c d : Fin n}
    (huc : ¬ G.Adj u c) (hud : ¬ G.Adj u d) (hcd : ¬ G.Adj c d) :
    graphFun G ∅ (fun v => decide (v = u ∨ v = c ∨ v = d)) = false := by
  rw [graphFun, Bool.or_eq_false_iff]
  constructor
  · simp
  · rw [decide_eq_false_iff_not]
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact G.loopless.irrefl _ hab
      | exact huc hab
      | exact huc hab.symm
      | exact hud hab
      | exact hud hab.symm
      | exact hcd hab
      | exact hcd hab.symm

lemma cross_star_not_filter {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (C D : Finset (Fin n))
    (hC : 2 ≤ C.card) (hD : 2 ≤ D.card) {ug uh vh : Fin n}
    (hvhD : vh ∈ D) (hgu : ug ≠ uh) (hgv : G.Adj ug vh)
    (hUhD : ∀ d ∈ D, G.Adj uh d) (hCVh : ∀ c ∈ C, G.Adj c vh)
    (hUgC : ∀ c ∈ C, ¬ G.Adj ug c) :
    ∃ x : Fin n → Bool, x ug = true ∧
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true) ∧ graphFun G ∅ x = false := by
  obtain ⟨c, hc, d, hd, huc, hud, hcd⟩ :=
    cross_star_independent_triple h4 C D hC hD hvhD hgu hgv hUhD hCVh hUgC
  refine ⟨fun v => decide (v = ug ∨ v = c ∨ v = d), by simp, ?_, ?_, ?_⟩
  · exact ⟨c, hc, by simp⟩
  · exact ⟨d, hd, by simp⟩
  · exact triple_input_graphFun_false huc hud hcd

lemma same_color_not_adj {n : ℕ} {G : SimpleGraph (Fin n)} (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) {u v : Fin n} (hcol : s u = s v) :
    ¬ G.Adj u v := fun h => hbip u v h hcol

lemma cross_star_not_mem_wmax {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (S T : Finset (Fin n))
    (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) {ug uh vh : Fin n}
    (hvhT : vh ∈ T) (hgu : ug ≠ uh) (hgv : G.Adj ug vh)
    (hUhT : ∀ d ∈ T, G.Adj uh d) (hSVh : ∀ c ∈ S, G.Adj c vh)
    (hUgS : ∀ c ∈ S, ¬ G.Adj ug c)
    (E : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ)
    (hprod : ∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n E h x = true ↔
      (∃ c ∈ S, x c = true) ∧ (∃ d ∈ T, x d = true)) :
    ug ∉ wmax G E h := by
  intro hmem
  have hfilter := (Finset.mem_filter.mp hmem).2
  obtain ⟨x, hux, hSx, hTx, hFx⟩ :=
    cross_star_not_filter h4 S T hS hT hvhT hgu hgv hUhT hSVh hUgS
  have ht := hfilter x ((hprod x).mpr ⟨hSx, hTx⟩) hux
  rw [hFx] at ht
  cases ht

end PEqualNP.Outside.L_meta_5012.OneFlagReview
