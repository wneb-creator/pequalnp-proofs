import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

namespace OneFlagReview

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

lemma exists_cross_nonedge {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (S T : Finset (Fin n))
    (hS : 2 ≤ S.card) (hT : 2 ≤ T.card) :
    ∃ s ∈ S, ∃ t ∈ T, ¬ G.Adj s t := by
  by_contra hnone
  push Not at hnone
  obtain ⟨s₁, hs₁, s₂, hs₂, hss⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨t₁, ht₁, t₂, ht₂, htt⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  exact htt (common_neighbors_unique h4 hss
    (hnone s₁ hs₁ t₁ ht₁) (hnone s₂ hs₂ t₁ ht₁)
    (hnone s₁ hs₁ t₂ ht₂) (hnone s₂ hs₂ t₂ ht₂))

lemma pair_input_graphFun_false {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {u v : Fin n} (huv : ¬ G.Adj u v) :
    graphFun G ∅ (PEqualNP.EdgeOwnership.pairInput u v) = false := by
  change graphFun G ∅ (fun z => decide (z = u ∨ z = v)) = false
  simpa only [or_self] using
    triple_input_graphFun_false (u := u) (c := v) (d := v) huv huv (G.loopless.irrefl v)

lemma raw_product_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (S T : Finset (Fin n))
    (hS : 2 ≤ S.card) (hT : 2 ≤ T.card)
    (E : PEqualNP.CircuitLowerBounds.Circuit) (h : ℕ)
    (hprod : ∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n E h x = true ↔
      (∃ s ∈ S, x s = true) ∧ (∃ t ∈ T, x t = true)) :
    ¬ BelowF G E h := by
  intro hbelow
  obtain ⟨s, hs, t, ht, hst⟩ := exists_cross_nonedge h4 S T hS hT
  have hgate := (hprod (PEqualNP.EdgeOwnership.pairInput s t)).mpr
    ⟨⟨s, hs, by simp [PEqualNP.EdgeOwnership.pairInput]⟩,
      ⟨t, ht, by simp [PEqualNP.EdgeOwnership.pairInput]⟩⟩
  have hfalse := hbelow (PEqualNP.EdgeOwnership.pairInput s t) hgate
  rw [pair_input_graphFun_false hst] at hfalse
  cases hfalse

end OneFlagReview


namespace SingletonReview

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.EdgeOwnership
  PEqualNP.MetaComplexity.NestedCover

lemma singleton_side_no_common_neighbor {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (B : Finset (Fin n))
    {u b₁ b₂ : Fin n} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂)
    (hu₁ : G.Adj u b₁) (hu₂ : G.Adj u b₂)
    (hbad : ∃ b ∈ B, ¬ G.Adj u b) :
    ¬ ∃ w : Fin n, ∀ b ∈ B, G.Adj w b := by
  rintro ⟨w, hw⟩
  have huw : u = w := by
    by_contra hneuw
    have hsmall := h4 u w hneuw
    have hlarge : 1 < (Finset.univ.filter fun b => G.Adj u b ∧ G.Adj w b).card := by
      exact Finset.one_lt_card.mpr
        ⟨b₁, by simp [hu₁, hw b₁ hb₁], b₂, by simp [hu₂, hw b₂ hb₂], hne⟩
    omega
  obtain ⟨b, hb, hub⟩ := hbad
  exact hub (huw ▸ hw b hb)

lemma independent_triple_input {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {b c d : Fin n}
    (hbc : ¬ G.Adj b c) (hbd : ¬ G.Adj b d) (hcd : ¬ G.Adj c d) :
    graphFun G ∅ (fun v => decide (v = b ∨ v = c ∨ v = d)) = false := by
  rw [graphFun, Bool.or_eq_false_iff]
  constructor
  · simp
  · rw [decide_eq_false_iff_not]
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    all_goals first
      | exact G.loopless.irrefl _ huv
      | exact hbc huv
      | exact hbc huv.symm
      | exact hbd huv
      | exact hbd huv.symm
      | exact hcd huv
      | exact hcd huv.symm

lemma raw_dirty_has_cross_nonedge {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (C D : Finset (Fin n)) (E : Circuit) (h : ℕ)
    (hraw : ∀ x : Fin n → Bool, gateVal n E h x = true ↔
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true))
    (hdirty : ¬ BelowF G E h) :
    ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d := by
  unfold BelowF at hdirty
  push Not at hdirty
  obtain ⟨x, hx, hFx⟩ := hdirty
  obtain ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩ := (hraw x).mp hx
  refine ⟨c, hc, d, hd, ?_⟩
  intro hcd
  apply hFx
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨c, d, hcd, hxc, hxd⟩

lemma unowned_side_product_negative_witness {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (B C D : Finset (Fin n))
    (hB : ¬ ∃ w : Fin n, ∀ b ∈ B, G.Adj w b)
    (hCD : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d) :
    ∃ x : Fin n → Bool, (∃ b ∈ B, x b = true) ∧
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true) ∧ graphFun G ∅ x = false := by
  obtain ⟨c, hc, d, hd, hcd⟩ := hCD
  have hnot : ¬ ∀ b ∈ B, G.Adj c b := fun h => hB ⟨c, h⟩
  push Not at hnot
  obtain ⟨b, hb, hcb⟩ := hnot
  refine ⟨fun v => decide (v = b ∨ v = c ∨ v = d), ?_, ?_, ?_, ?_⟩
  · exact ⟨b, hb, by simp⟩
  · exact ⟨c, hc, by simp⟩
  · exact ⟨d, hd, by simp⟩
  · exact independent_triple_input (fun h => hcb h.symm) (hBD b hb d hd) hcd

lemma same_side_product_negative_witness {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (B C D : Finset (Fin n))
    (hB : ¬ ∃ w : Fin n, ∀ b ∈ B, G.Adj w b)
    (hCD : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hcolor : ∀ b ∈ B, ∀ d ∈ D, s b = s d) :
    ∃ x : Fin n → Bool, (∃ b ∈ B, x b = true) ∧
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true) ∧ graphFun G ∅ x = false := by
  apply unowned_side_product_negative_witness B C D hB hCD
  intro b hb d hd hbd
  exact hbip b d hbd (hcolor b hb d hd)

lemma or_side_times_dirty_raw_product_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (B C D : Finset (Fin n))
    (hB : ¬ ∃ w : Fin n, ∀ b ∈ B, G.Adj w b)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (E : Circuit) (h k : ℕ)
    (hraw : ∀ x : Fin n → Bool, gateVal n E h x = true ↔
      (∃ c ∈ C, x c = true) ∧ (∃ d ∈ D, x d = true))
    (hdirty : ¬ BelowF G E h)
    (hproduct : ∀ x : Fin n → Bool, gateVal n E k x = true ↔
      (∃ b ∈ B, x b = true) ∧ gateVal n E h x = true) :
    ¬ BelowF G E k := by
  obtain ⟨x, hBx, hCx, hDx, hFx⟩ := unowned_side_product_negative_witness B C D hB
    (raw_dirty_has_cross_nonedge C D E h hraw hdirty) hBD
  intro hbelow
  have hgood := hbelow x ((hproduct x).mpr ⟨hBx, (hraw x).mpr ⟨hCx, hDx⟩⟩)
  rw [hFx] at hgood
  cases hgood

lemma dirty_singleton_side_no_common_neighbor {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (B : Finset (Fin n))
    {u b₁ b₂ : Fin n} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B) (hne : b₁ ≠ b₂)
    (hu₁ : G.Adj u b₁) (hu₂ : G.Adj u b₂) (E : Circuit) (g : ℕ)
    (hraw : ∀ x : Fin n → Bool, gateVal n E g x = true ↔
      x u = true ∧ ∃ b ∈ B, x b = true) (hdirty : ¬ BelowF G E g) :
    ¬ ∃ w : Fin n, ∀ b ∈ B, G.Adj w b := by
  apply singleton_side_no_common_neighbor h4 B hb₁ hb₂ hne hu₁ hu₂
  unfold BelowF at hdirty
  push Not at hdirty
  obtain ⟨x, hx, hFx⟩ := hdirty
  obtain ⟨hxu, b, hb, hxb⟩ := (hraw x).mp hx
  refine ⟨b, hb, ?_⟩
  intro hub
  apply hFx
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr ⟨u, b, hub, hxu, hxb⟩

end SingletonReview

end PEqualNP.Outside.L_meta_5012
