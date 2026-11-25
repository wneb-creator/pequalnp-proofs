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


namespace OverlapBoundaryReview

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma raw_filter_adjacent_overlap {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (A B : Finset (Fin n)) {t v : Fin n}
    (hv : v ∈ A ∩ B)
    (hsafe : ∀ x : Fin n → Bool, (∃ a ∈ A, x a = true) →
      (∃ b ∈ B, x b = true) → x t = true → graphFun G ∅ x = true) :
    G.Adj t v := by
  by_contra htv
  have ht := hsafe (pairInput t v)
    ⟨v, (Finset.mem_inter.mp hv).1, by simp [pairInput]⟩
    ⟨v, (Finset.mem_inter.mp hv).2, by simp [pairInput]⟩ (by simp [pairInput])
  rw [OneFlagReview.pair_input_graphFun_false htv] at ht
  cases ht

lemma overlap_filter_boundary {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (I T J : Finset (Fin n))
    (w : Fin n) (hI : ∀ i ∈ I, G.Adj w i) (hJ : J.Nonempty)
    (hTJ : ∀ t ∈ T, ∀ j ∈ J, G.Adj t j) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  by_cases hc : (T ∩ I).card ≤ 1
  · exact Or.inr hc
  · obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (T ∩ I).card)
    obtain ⟨j, hj⟩ := hJ
    have hwj := OneFlagReview.common_neighbors_unique h4 hab
      (hI a (Finset.mem_inter.mp ha).2).symm
      (hI b (Finset.mem_inter.mp hb).2).symm
      (hTJ a (Finset.mem_inter.mp ha).1 j hj)
      (hTJ b (Finset.mem_inter.mp hb).1 j hj)
    left
    intro t ht
    simpa only [hwj] using (hTJ t ht j hj).symm

lemma raw_product_filter_boundary {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) (I T A B : Finset (Fin n))
    (w : Fin n) (hI : ∀ i ∈ I, G.Adj w i) (hAB : (A ∩ B).Nonempty)
    (hfilter : ∀ t ∈ T, ∀ x : Fin n → Bool, (∃ a ∈ A, x a = true) →
      (∃ b ∈ B, x b = true) → x t = true → graphFun G ∅ x = true) :
    (∀ t ∈ T, G.Adj w t) ∨ (T ∩ I).card ≤ 1 := by
  apply overlap_filter_boundary h4 I T (A ∩ B) w hI hAB
  intro t ht j hj
  exact raw_filter_adjacent_overlap A B hj (hfilter t ht)

end OverlapBoundaryReview


namespace Projection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]


def setOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

lemma setOr_union {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    setOr (S ∪ T) x = (setOr S x || setOr T x) := by
  simp [setOr, Finset.mem_union, or_and_right, exists_or]

noncomputable def projectedWire {n : ℕ} (P : Finset (Fin n))
    (S : ℕ → Finset (Fin n)) (w : ℕ) : Option ℕ :=
  if h : (S w ∩ P).Nonempty then
    if 2 ≤ (S w ∩ P).card then some w else some ((S w ∩ P).min' h).val
  else none

lemma projectedWire_bound {n : ℕ} (P : Finset (Fin n))
    (S : ℕ → Finset (Fin n)) {j w v : ℕ} (hw : w < n + j)
    (hv : projectedWire P S w = some v) : v < n + j := by
  unfold projectedWire at hv
  split_ifs at hv with h htwo
  · cases hv; exact hw
  · cases hv
    exact lt_of_lt_of_le (Fin.isLt _) (Nat.le_add_right _ _)

def repairOr (old : Gate) : Option ℕ → Option ℕ → Gate
  | some a, some b => ⟨GateOp.or, [a, b]⟩
  | some a, none => ⟨GateOp.or, [a, a]⟩
  | none, some b => ⟨GateOp.or, [b, b]⟩
  | none, none => old

lemma repairOr_op {old : Gate} (hop : old.op = GateOp.or) (a b : Option ℕ) :
    (repairOr old a b).op = old.op := by
  cases a <;> cases b <;> simp [repairOr, hop]

lemma repairOr_length {old : Gate} (hlen : old.inputs.length = 2) (a b : Option ℕ) :
    (repairOr old a b).inputs.length = 2 := by
  cases a <;> cases b <;> simp [repairOr, hlen]

lemma repairOr_back {old : Gate} {N : ℕ} (hold : ∀ w ∈ old.inputs, w < N)
    (a b : Option ℕ) (ha : ∀ w, a = some w → w < N)
    (hb : ∀ w, b = some w → w < N) :
    ∀ w ∈ (repairOr old a b).inputs, w < N := by
  cases a with
  | none =>
    cases b with
    | none => exact hold
    | some b => simpa [repairOr] using hb b rfl
  | some a =>
    cases b with
    | none => simpa [repairOr] using ha a rfl
    | some b =>
      intro w hw
      simp only [repairOr, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ha _ rfl
      · exact hb _ rfl

noncomputable def rebuild (C : Circuit) (R : Finset ℕ) (p : ℕ → Option ℕ) : Circuit :=
  ⟨List.ofFn (fun j : Fin C.gates.length => if j.val ∈ R then
    repairOr (gateAt C j.val) (p (opnd C j.val 0)) (p (opnd C j.val 1))
    else gateAt C j.val), C.output⟩

lemma rebuild_length (C : Circuit) (R : Finset ℕ) (p : ℕ → Option ℕ) :
    (rebuild C R p).gates.length = C.gates.length := by
  simp [rebuild]

lemma gateAt_rebuild (C : Circuit) (R : Finset ℕ) (p : ℕ → Option ℕ)
    {j : ℕ} (hj : j < C.gates.length) :
    gateAt (rebuild C R p) j = if j ∈ R then
      repairOr (gateAt C j) (p (opnd C j 0)) (p (opnd C j 1)) else gateAt C j := by
  simp [rebuild, gateAt, List.getD_eq_getElem?_getD, hj]

lemma rebuild_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R : Finset ℕ) (p : ℕ → Option ℕ)
    (hR : ∀ j ∈ R, (gateAt C j).op = GateOp.or)
    (hp : ∀ j < C.gates.length, ∀ w < n + j, ∀ v, p w = some v → v < n + j) :
    IsAO2 n (rebuild C R p) := by
  have hOp : ∀ j < C.gates.length,
      (gateAt (rebuild C R p) j).op = (gateAt C j).op := by
    intro j hj
    rw [gateAt_rebuild C R p hj]
    split_ifs with h
    · exact repairOr_op (hR j h) _ _
    · rfl
  have hLen : ∀ j < C.gates.length,
      (gateAt (rebuild C R p) j).inputs.length = 2 := by
    intro j hj
    have hold := hAO.2.2 _ (gateAt_mem hj)
    rw [gateAt_rebuild C R p hj]
    split_ifs
    · exact repairOr_length hold _ _
    · exact hold
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hjC : j < C.gates.length := by simpa [rebuild_length] using hj
    have hget := gateAt_eq (C := rebuild C R p) hj
    rw [← hget, hOp j hjC]
    exact hAO.1 _ (gateAt_mem hjC)
  · intro j hj w hw
    have hjC : j < C.gates.length := by simpa [rebuild_length] using hj
    rw [gateAt_rebuild C R p hjC] at hw
    split_ifs at hw with h
    · exact repairOr_back (hAO.2.1 j hjC) _ _
        (fun v hv => hp j hjC _ (opnd_lt hAO hjC 0) v hv)
        (fun v hv => hp j hjC _ (opnd_lt hAO hjC 1) v hv) w hw
    · exact hAO.2.1 j hjC w hw
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
    have hjC : j < C.gates.length := by simpa [rebuild_length] using hj
    rw [← gateAt_eq hj]
    exact hLen j hjC

lemma rebuild_size (C : Circuit) (R : Finset ℕ) (p : ℕ → Option ℕ) :
    (rebuild C R p).size = C.size := rebuild_length C R p

def selected {α : Type} [DecidableEq α] (P S : Finset α) : Prop :=
  ¬ S ⊆ P ∧ 2 ≤ (S ∩ P).card

lemma projected_mono {α : Type} [DecidableEq α] {P S T : Finset α}
    (hST : S ⊆ T) : S ∩ P ⊆ T ∩ P := by
  intro a ha
  exact Finset.mem_inter.mpr ⟨hST (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩

lemma selected_mono {α : Type} [DecidableEq α] {P S T : Finset α}
    (hST : S ⊆ T) (hS : selected P S) : selected P T := by
  refine ⟨fun hTP => hS.1 (hST.trans hTP), ?_⟩
  exact hS.2.trans (Finset.card_le_card (projected_mono hST))

lemma unselected_of_subset {α : Type} [DecidableEq α] {P S T : Finset α}
    (hST : S ⊆ T) (hT : ¬ selected P T) : ¬ selected P S := by
  exact fun hS => hT (selected_mono hST hS)

lemma unselected_cases {α : Type} [DecidableEq α] (P S : Finset α)
    (hS : ¬ selected P S) : S ⊆ P ∨ (S ∩ P).card ≤ 1 := by
  by_cases hsub : S ⊆ P
  · exact Or.inl hsub
  · right
    have hcard : ¬ 2 ≤ (S ∩ P).card := fun h => hS ⟨hsub, h⟩
    omega

lemma projected_eq_of_subset {α : Type} [DecidableEq α] {P S : Finset α}
    (hSP : S ⊆ P) : S ∩ P = S := by
  ext a
  simp only [Finset.mem_inter]
  exact ⟨And.left, fun ha => ⟨ha, hSP ha⟩⟩

lemma projected_union {α : Type} [DecidableEq α] (P S T : Finset α) :
    (S ∪ T) ∩ P = (S ∩ P) ∪ (T ∩ P) := by
  ext a
  simp only [Finset.mem_inter, Finset.mem_union]
  tauto

lemma union_selected_left {α : Type} [DecidableEq α] {P S T : Finset α}
    (hS : selected P S) : selected P (S ∪ T) :=
  selected_mono Finset.subset_union_left hS

lemma union_selected_right {α : Type} [DecidableEq α] {P S T : Finset α}
    (hT : selected P T) : selected P (S ∪ T) :=
  selected_mono Finset.subset_union_right hT

lemma union_unselected_children {α : Type} [DecidableEq α] {P S T : Finset α}
    (h : ¬ selected P (S ∪ T)) : ¬ selected P S ∧ ¬ selected P T :=
  ⟨fun hS => h (union_selected_left hS), fun hT => h (union_selected_right hT)⟩

lemma selected_projected_nonempty {α : Type} [DecidableEq α] {P S : Finset α}
    (h : selected P S) : (S ∩ P).Nonempty :=
  Finset.card_pos.mp (by have := h.2; omega)

lemma selected_union_nonempty_child {α : Type} [DecidableEq α] {P S T : Finset α}
    (h : selected P (S ∪ T)) : (S ∩ P).Nonempty ∨ (T ∩ P).Nonempty := by
  have hp := selected_projected_nonempty h
  rw [projected_union] at hp
  exact Finset.union_nonempty.mp hp

lemma selected_union_not_both_empty {α : Type} [DecidableEq α] {P S T : Finset α}
    (h : selected P (S ∪ T)) : ¬ (S ∩ P = ∅ ∧ T ∩ P = ∅) := by
  rintro ⟨hS, hT⟩
  rcases selected_union_nonempty_child h with hs | ht
  · simp [hS] at hs
  · simp [hT] at ht

lemma projected_eq_singleton {α : Type} [DecidableEq α] {P S : Finset α} {a : α}
    (hcard : (S ∩ P).card ≤ 1) (ha : a ∈ S ∩ P) : S ∩ P = {a} := by
  ext b
  simp only [Finset.mem_singleton]
  constructor
  · intro hb
    exact Finset.card_le_one.mp hcard b hb a ha
  · rintro rfl
    exact ha

lemma unselected_nontrivial_all_good {α : Type} [DecidableEq α] {P S : Finset α}
    (hS : ¬ selected P S) (hcard : 2 ≤ (S ∩ P).card) : S ⊆ P := by
  by_contra hsub
  exact hS ⟨hsub, hcard⟩


def optionVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Option ℕ) : Bool :=
  p.elim false (wval C x)

lemma projectedWire_none_iff {n : ℕ} (P : Finset (Fin n))
    (S : ℕ → Finset (Fin n)) (w : ℕ) :
    projectedWire P S w = none ↔ S w ∩ P = ∅ := by
  classical
  unfold projectedWire
  split_ifs with hn hc
  · simp only [false_iff]
    exact Finset.Nonempty.ne_empty hn
  · simp only [false_iff]
    exact Finset.Nonempty.ne_empty hn
  · simp only [true_iff]
    exact Finset.not_nonempty_iff_eq_empty.mp hn

open Classical in
lemma projectedWire_value {n : ℕ} (P : Finset (Fin n))
    (S : ℕ → Finset (Fin n)) (D : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : wval D x w = if selected P (S w) then setOr (S w ∩ P) x else setOr (S w) x) :
    optionVal D x (projectedWire P S w) = setOr (S w ∩ P) x := by
  classical
  unfold projectedWire
  split_ifs with hn hc
  · change wval D x w = _
    rw [hw]
    by_cases hs : selected P (S w)
    · simp [hs]
    · have hsub := unselected_nontrivial_all_good hs hc
      simp [hs, projected_eq_of_subset hsub]
  · change wval D x ((S w ∩ P).min' hn).val = _
    rw [wval_input D x _ (Fin.isLt _)]
    have hsmall : (S w ∩ P).card ≤ 1 := by omega
    have hs := projected_eq_singleton hsmall (Finset.min'_mem _ hn)
    conv_rhs => rw [hs]
    simp [setOr]
  · have he : S w ∩ P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [optionVal, setOr, he]

lemma binary_or_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j a b : ℕ} (hj : j < C.gates.length)
    (hgate : gateAt C j = ⟨GateOp.or, [a, b]⟩) (x : Fin n → Bool) :
    wval C x (n + j) = (wval C x a || wval C x b) := by
  have h := wval_gate_eval hAO x hj
  simpa [hgate, opnd, GateOp.eval] using h

lemma repairOr_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (old : Gate) (a b : Option ℕ)
    (hgate : gateAt C j = repairOr old a b) (hn : a ≠ none ∨ b ≠ none)
    (x : Fin n → Bool) :
    wval C x (n + j) = (optionVal C x a || optionVal C x b) := by
  cases a with
  | none =>
    cases b with
    | none => simp at hn
    | some b =>
      have h := binary_or_value hAO hj hgate x
      simpa [optionVal] using h
  | some a =>
    cases b with
    | none =>
      have h := binary_or_value hAO hj hgate x
      simpa [optionVal] using h
    | some b =>
      exact binary_or_value hAO hj hgate x


open Classical in
lemma rebuild_pure_cone_values {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (Q R : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, (w < n ∨ w - n ∈ Q) →
      wval (rebuild C R (projectedWire P S)) x w =
        if selected P (S w) then setOr (S w ∩ P) x else setOr (S w) x := by
  classical
  let D := rebuild C R (projectedWire P S)
  have hD : IsAO2 n D := rebuild_isAO2 hAO R (projectedWire P S)
    (fun j hj => (hQ j ((hR j).mp hj).1).1)
    (fun j _ w hw v hv => projectedWire_bound P S hw hv)
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdom
    by_cases hwn : w < n
    · have hs := hSin w hwn
      have hn : ¬ selected P (S w) := by
        intro hh
        have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := S w) (s₂ := P))
        rw [hs, Finset.card_singleton] at hle
        have hcard := hh.2
        rw [hs] at hcard
        omega
      rw [ite_eq_right hn, wval_input _ x w hwn, hs]
      simp [setOr]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hq : j ∈ Q := by simpa using hdom.resolve_left hwn
      obtain ⟨hop, hsupport, hchildren⟩ := hQ j hq
      have ha := opnd_lt hAO hj 0
      have hb := opnd_lt hAO hj 1
      have hia := ih (opnd C j 0) ha (by omega) (hchildren 0)
      have hib := ih (opnd C j 1) hb (by omega) (hchildren 1)
      have hjD : j < D.gates.length := by simpa [D, rebuild_length] using hj
      by_cases hsel : selected P (S (n + j))
      · have hr : j ∈ R := (hR j).mpr ⟨hq, hsel⟩
        have hg : gateAt D j = repairOr (gateAt C j)
            (projectedWire P S (opnd C j 0)) (projectedWire P S (opnd C j 1)) := by
          simp only [D, gateAt_rebuild C R (projectedWire P S) hj, ite_eq_left hr]
        have hn : projectedWire P S (opnd C j 0) ≠ none ∨
            projectedWire P S (opnd C j 1) ≠ none := by
          have hs : selected P (S (opnd C j 0) ∪ S (opnd C j 1)) := hsupport ▸ hsel
          rcases selected_union_nonempty_child hs with he | he
          · left
            intro heq
            exact he.ne_empty ((projectedWire_none_iff P S _).mp heq)
          · right
            intro heq
            exact he.ne_empty ((projectedWire_none_iff P S _).mp heq)
        rw [ite_eq_left hsel]
        change wval D x (n + j) = _
        rw [repairOr_value hD hjD _ _ _ hg hn x,
          projectedWire_value P S D x _ hia, projectedWire_value P S D x _ hib,
          hsupport, projected_union, setOr_union]
      · have hr : j ∉ R := fun hr => hsel ((hR j).mp hr).2
        have hg : gateAt D j = gateAt C j := by
          simp only [D, gateAt_rebuild C R (projectedWire P S) hj, ite_eq_right hr]
        have hnchildren : ¬ selected P (S (opnd C j 0)) ∧
            ¬ selected P (S (opnd C j 1)) := by
          apply union_unselected_children
          rwa [← hsupport]
        have hgate : gateAt D j = ⟨GateOp.or, [opnd C j 0, opnd C j 1]⟩ := by
          rw [hg]
          have hin := gate_inputs_eq hAO hj
          cases he : gateAt C j with
          | mk o ins =>
            simp only [he] at hop hin
            simp only [hop, hin]
        rw [ite_eq_right hsel]
        change wval D x (n + j) = _
        rw [binary_or_value hD hjD hgate x, hia, hib,
          ite_eq_right hnchildren.1, ite_eq_right hnchildren.2, hsupport, setOr_union]


/-- The old values in a hereditary pure OR cone are exactly its raw supports. -/
lemma pure_cone_values {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (Q : Finset ℕ) (S : ℕ → Finset (Fin n))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, (w < n ∨ w - n ∈ Q) →
      wval C x w = setOr (S w) x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdom
    by_cases hwn : w < n
    · rw [wval_input C x w hwn, hSin w hwn]
      simp [setOr]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hq : j ∈ Q := by simpa using hdom.resolve_left hwn
      obtain ⟨hop, hsupport, hchildren⟩ := hQ j hq
      have ha := opnd_lt hAO hj 0
      have hb := opnd_lt hAO hj 1
      rw [wval_gate_or hAO x hj hop,
        ih (opnd C j 0) ha (by omega) (hchildren 0),
        ih (opnd C j 1) hb (by omega) (hchildren 1), hsupport, setOr_union]

lemma binary_eval_mono {op : GateOp} (hop : op = GateOp.and ∨ op = GateOp.or)
    {a b c d : Bool} (ha : c = true → a = true) (hb : d = true → b = true)
    (h : op.eval [c, d] = true) : op.eval [a, b] = true := by
  rcases hop with rfl | rfl <;>
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all [GateOp.eval]

/-- Pointwise decreases at the changed gate slots propagate through an AO2 circuit. -/
lemma global_decrease_of_local {n : ℕ} {C D : Circuit}
    (hC : IsAO2 n C) (hD : IsAO2 n D) (hlen : D.gates.length = C.gates.length)
    (R : Finset ℕ)
    (hsame : ∀ j < C.gates.length, j ∉ R → gateAt D j = gateAt C j)
    (hlocal : ∀ j < C.gates.length, j ∈ R → ∀ x : Fin n → Bool,
      wval D x (n + j) = true → wval C x (n + j) = true)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, wval D x w = true → wval C x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv
    by_cases hwn : w < n
    · rw [wval_input D x w hwn] at hv
      rwa [wval_input C x w hwn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hr : j ∈ R
      · exact hlocal j hj hr x hv
      · have hg := hsame j hj hr
        have hjD : j < D.gates.length := by omega
        have he := wval_gate_eval hD x hjD
        simp only [opnd, hg] at he
        rw [he] at hv
        rw [wval_gate_eval hC x hj]
        exact binary_eval_mono (hC.1 _ (gateAt_mem hj))
          (ih _ (opnd_lt hC hj 0) (by have := opnd_lt hC hj 0; omega))
          (ih _ (opnd_lt hC hj 1) (by have := opnd_lt hC hj 1; omega)) hv

/-- Every wire only decreases after projection, including gates outside the pure OR cone. -/
lemma rebuild_decreases {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (Q R : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length,
      wval (rebuild C R (projectedWire P S)) x w = true → wval C x w = true := by
  classical
  let D := rebuild C R (projectedWire P S)
  have hD : IsAO2 n D := rebuild_isAO2 hAO R (projectedWire P S)
    (fun j hj => (hQ j ((hR j).mp hj).1).1)
    (fun j _ w hw v hv => projectedWire_bound P S hw hv)
  apply global_decrease_of_local hAO hD (rebuild_length C R (projectedWire P S)) R
  · intro j hj hr
    simp only [D, gateAt_rebuild C R (projectedWire P S) hj, ite_eq_right hr]
  · intro j hj hr y hy
    have hq := ((hR j).mp hr).1
    have hsel := ((hR j).mp hr).2
    have hdom : n + j < n ∨ n + j - n ∈ Q := Or.inr (by simpa using hq)
    have hp := rebuild_pure_cone_values hAO Q R P S hR hSin hQ y (n+j) (by omega) hdom
    rw [ite_eq_left hsel] at hp
    change wval D y (n + j) = _ at hp
    rw [hp] at hy
    rw [pure_cone_values hAO Q S hSin hQ y (n+j) (by omega) hdom]
    simp only [setOr, decide_eq_true_eq] at hy ⊢
    obtain ⟨v, hv, hyv⟩ := hy
    exact ⟨v, (Finset.mem_inter.mp hv).1, hyv⟩


/-- If all direct exits from the modified region go to `g`, equality at `g` on a
fixed input propagates to every other wire outside the region. -/
lemma outside_region_values {n : ℕ} {C D : Circuit}
    (hC : IsAO2 n C) (hD : IsAO2 n D) (hlen : D.gates.length = C.gates.length)
    (R : Finset ℕ) (g : ℕ)
    (hsame : ∀ j < C.gates.length, j ∉ R → gateAt D j = gateAt C j)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (x : Fin n → Bool) (hg : wval D x (n + g) = wval C x (n + g)) :
    ∀ w < n + C.gates.length, (w < n ∨ w - n ∉ R) → wval D x w = wval C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdom
    by_cases hwn : w < n
    · rw [wval_input D x w hwn, wval_input C x w hwn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hr : j ∉ R := by simpa using hdom.resolve_left hwn
      by_cases hjg : j = g
      · simpa [hjg] using hg
      · have hgate := hsame j hj hr
        have hjD : j < D.gates.length := by omega
        have he := wval_gate_eval hD x hjD
        simp only [opnd, hgate] at he
        have hi0 := ih (opnd C j 0) (opnd_lt hC hj 0)
          (by have := opnd_lt hC hj 0; omega) (hexit j hj hr hjg 0)
        have hi1 := ih (opnd C j 1) (opnd_lt hC hj 1)
          (by have := opnd_lt hC hj 1; omega) (hexit j hj hr hjg 1)
        rw [he, wval_gate_eval hC x hj]
        change (gateAt C j).op.eval [wval D x (opnd C j 0), wval D x (opnd C j 1)] = _
        rw [hi0, hi1]

lemma not_selected_singleton {n : ℕ} (P : Finset (Fin n)) (u : Fin n) :
    ¬ selected P {u} := by
  intro h
  have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := {u}) (s₂ := P))
  simp only [Finset.card_singleton] at hle
  have := h.2
  omega

/-- Projecting the pure OR operand of a singleton product realizes the clean product
without adding a gate. The singleton operand may itself be a shared OR cone. -/
lemma rebuilt_singleton_product {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (Q R : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (g : ℕ) (hg : g < C.gates.length) (hgop : (gateAt C g).op = GateOp.and)
    (hgdom : ∀ b : Fin 2, opnd C g b < n ∨ opnd C g b - n ∈ Q)
    (u : Fin n) (hsingle : S (opnd C g 0) = {u})
    (hlarge : selected P (S (opnd C g 1))) (x : Fin n → Bool) :
    wval (rebuild C R (projectedWire P S)) x (n + g) =
      (x u && setOr (S (opnd C g 1) ∩ P) x) := by
  classical
  let D := rebuild C R (projectedWire P S)
  have hD : IsAO2 n D := rebuild_isAO2 hAO R (projectedWire P S)
    (fun j hj => (hQ j ((hR j).mp hj).1).1)
    (fun j _ w hw v hv => projectedWire_bound P S hw hv)
  have hgr : g ∉ R := by
    intro h
    have ho := (hQ g ((hR g).mp h).1).1
    rw [hgop] at ho
    cases ho
  have hgate : gateAt D g = gateAt C g := by
    simp only [D, gateAt_rebuild C R (projectedWire P S) hg, ite_eq_right hgr]
  have hgD : g < D.gates.length := by simpa [D, rebuild_length] using hg
  have he := wval_gate_eval hD x hgD
  simp only [opnd, hgate] at he
  have ha := opnd_lt hAO hg 0
  have hb := opnd_lt hAO hg 1
  have hv0 := rebuild_pure_cone_values hAO Q R P S hR hSin hQ x
    (opnd C g 0) (by omega) (hgdom 0)
  have hv1 := rebuild_pure_cone_values hAO Q R P S hR hSin hQ x
    (opnd C g 1) (by omega) (hgdom 1)
  have hn : ¬ selected P (S (opnd C g 0)) := by
    rw [hsingle]
    exact not_selected_singleton P u
  change wval D x (n + g) = _
  rw [he, hgop]
  simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  change (wval D x (opnd C g 0) && wval D x (opnd C g 1)) = _
  rw [hv0, hv1, ite_eq_right hn, ite_eq_left hlarge, hsingle]
  simp [setOr]

lemma original_singleton_product {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (Q : Finset ℕ) (S : ℕ → Finset (Fin n))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (g : ℕ) (hg : g < C.gates.length) (hgop : (gateAt C g).op = GateOp.and)
    (hgdom : ∀ b : Fin 2, opnd C g b < n ∨ opnd C g b - n ∈ Q)
    (u : Fin n) (hsingle : S (opnd C g 0) = {u}) (x : Fin n → Bool) :
    wval C x (n + g) = (x u && setOr (S (opnd C g 1)) x) := by
  rw [wval_gate_and hAO x hg hgop]
  have ha := opnd_lt hAO hg 0
  have hb := opnd_lt hAO hg 1
  rw [pure_cone_values hAO Q S hSin hQ x _ (by omega) (hgdom 0),
    pure_cone_values hAO Q S hSin hQ x _ (by omega) (hgdom 1), hsingle]
  simp [setOr]

lemma singleton_neighborhood_projection_pair {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B : Finset (Fin n)) (u v w : Fin n)
    (huB : u ∉ B) (hvw : G.Adj v w) :
    (pairInput v w u && setOr B (pairInput v w)) =
    (pairInput v w u && setOr (B ∩ (Finset.univ.filter fun t => G.Adj u t))
      (pairInput v w)) := by
  cases hu : pairInput v w u with
  | false => simp
  | true =>
    simp only [Bool.true_and, setOr, decide_eq_decide]
    constructor
    · rintro ⟨b, hb, hbx⟩
      have huu : u = v ∨ u = w := by
        simpa only [pairInput, decide_eq_true_eq] using hu
      have hbb : b = v ∨ b = w := by
        simpa only [pairInput, decide_eq_true_eq] using hbx
      have hub : G.Adj u b := by
        rcases huu with rfl | rfl <;> rcases hbb with rfl | rfl
        · exact False.elim (huB hb)
        · exact hvw
        · exact hvw.symm
        · exact False.elim (huB hb)
      exact ⟨b, Finset.mem_inter.mpr ⟨hb, by simp [hub]⟩, hbx⟩
    · rintro ⟨b, hb, hbx⟩
      exact ⟨b, (Finset.mem_inter.mp hb).1, hbx⟩

lemma projected_singleton_clean {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B : Finset (Fin n)) (u : Fin n) (x : Fin n → Bool)
    (h : (x u && setOr (B ∩ (Finset.univ.filter fun t => G.Adj u t)) x) = true) :
    graphFun G ∅ x = true := by
  simp only [Bool.and_eq_true, setOr, decide_eq_true_eq] at h
  obtain ⟨hu, b, hb, hbx⟩ := h
  have hub : G.Adj u b := by simpa using (Finset.mem_inter.mp hb).2
  unfold graphFun
  rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact Or.inr ⟨u, b, hub, hu, hbx⟩


/-- A hereditary domain containing no changed gate has identical values. -/
lemma unchanged_domain_values {n : ℕ} {C D : Circuit}
    (hC : IsAO2 n C) (hD : IsAO2 n D) (hlen : D.gates.length = C.gates.length)
    (A R : Finset ℕ)
    (hsame : ∀ j < C.gates.length, j ∉ R → gateAt D j = gateAt C j)
    (hA : ∀ j ∈ A, j ∉ R ∧ ∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ A)
    (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, (w < n ∨ w - n ∈ A) → wval D x w = wval C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdom
    by_cases hwn : w < n
    · rw [wval_input D x w hwn, wval_input C x w hwn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      have hjA : j ∈ A := by simpa using hdom.resolve_left hwn
      have hgate := hsame j hj (hA j hjA).1
      have hjD : j < D.gates.length := by omega
      have he := wval_gate_eval hD x hjD
      simp only [opnd, hgate] at he
      have hi0 := ih (opnd C j 0) (opnd_lt hC hj 0)
        (by have := opnd_lt hC hj 0; omega) ((hA j hjA).2 0)
      have hi1 := ih (opnd C j 1) (opnd_lt hC hj 1)
        (by have := opnd_lt hC hj 1; omega) ((hA j hjA).2 1)
      rw [he, wval_gate_eval hC x hj]
      change (gateAt C j).op.eval [wval D x (opnd C j 0), wval D x (opnd C j 1)] = _
      rw [hi0, hi1]

lemma wval_input_mono {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv
    by_cases hwn : w < n
    · rw [wval_input C x w hwn] at hv
      rw [wval_input C y w hwn]
      exact hxy _ hv
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      rw [wval_gate_eval hC x hj] at hv
      rw [wval_gate_eval hC y hj]
      exact binary_eval_mono (hC.1 _ (gateAt_mem hj))
        (ih _ (opnd_lt hC hj 0) (by have := opnd_lt hC hj 0; omega))
        (ih _ (opnd_lt hC hj 1) (by have := opnd_lt hC hj 1; omega)) hv

lemma circuitFun_input_mono {n : ℕ} {C : Circuit} (hC : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true)
    (hx : circuitFun n C x = true) : circuitFun n C y = true := by
  change wval C x C.output = true at hx
  change wval C y C.output = true
  by_cases hout : C.output < n + C.gates.length
  · exact wval_input_mono hC x y hxy _ hout hx
  · rw [wval_ge_len C x (by omega)] at hx
    cases hx

/-- For a monotone circuit, accepting each graph edge suffices for completeness. -/
lemma graphFun_preserved_of_edges {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C D : Circuit} (hD : IsAO2 n D)
    (hfun : circuitFun n C = graphFun G ∅)
    (hle : ∀ x, circuitFun n D x = true → circuitFun n C x = true)
    (hedge : ∀ v w, G.Adj v w → circuitFun n D (pairInput v w) =
      circuitFun n C (pairInput v w)) : circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← hfun]
    exact hle x hx
  · intro hx
    have hx' : ∃ v w, G.Adj v w ∧ x v = true ∧ x w = true := by
      simpa [graphFun] using hx
    obtain ⟨v, w, hvw, hv, hw⟩ := hx'
    have hpair : circuitFun n D (pairInput v w) = true := by
      rw [hedge v w hvw, hfun]
      unfold graphFun
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact Or.inr ⟨v, w, hvw, by simp [pairInput], by simp [pairInput]⟩
    apply circuitFun_input_mono hD (pairInput v w) x _ hpair
    intro t ht
    have ht' : t = v ∨ t = w := by simpa only [pairInput, decide_eq_true_eq] using ht
    rcases ht' with rfl | rfl
    · exact hv
    · exact hw


/-- Conditional singleton compiler. `Q` supplies the hereditary pure OR domain and
its exact supports. `R` selects its mixed nodes with at least two retained variables.
`hexit` states full direct-exit privacy, including exits to OR gates. `A` is an
unchanged hereditary ancestor domain containing the other junk gate `h`.

These are explicit sufficient hypotheses; this theorem does not derive privacy
from bipartiteness, the four-cycle condition, or the shape of another junk gate. -/
lemma singleton_projection_compiler {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    (Q R A : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (g h : ℕ) (hg : g < C.gates.length) (hh : h < C.gates.length)
    (hgop : (gateAt C g).op = GateOp.and)
    (hgdom : ∀ b : Fin 2, opnd C g b < n ∨ opnd C g b - n ∈ Q)
    (u : Fin n) (hsingle : S (opnd C g 0) = {u})
    (hlarge : selected P (S (opnd C g 1)))
    (hP : P = Finset.univ.filter fun t => G.Adj u t)
    (huB : u ∉ S (opnd C g 1))
    (hhA : h ∈ A)
    (hA : ∀ j ∈ A, j ∉ R ∧ ∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ A)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (hout : C.output < n ∨ C.output - n ∉ R)
    (hfun : circuitFun n C = graphFun G ∅) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ x, gateVal n D g x = true → graphFun G ∅ x = true) ∧
      (∀ x, gateVal n D h x = gateVal n C h x) ∧
      (∀ j < C.gates.length, (gateAt D j).op = (gateAt C j).op) ∧
      (∀ j, IsDirtyAnd n G D j → IsDirtyAnd n G C j) := by
  classical
  let D := rebuild C R (projectedWire P S)
  have hD : IsAO2 n D := rebuild_isAO2 hAO R (projectedWire P S)
    (fun j hj => (hQ j ((hR j).mp hj).1).1)
    (fun j _ w hw v hv => projectedWire_bound P S hw hv)
  have hlen : D.gates.length = C.gates.length := rebuild_length C R (projectedWire P S)
  have hsame : ∀ j < C.gates.length, j ∉ R → gateAt D j = gateAt C j := by
    intro j hj hr
    simp only [D, gateAt_rebuild C R (projectedWire P S) hj, ite_eq_right hr]
  have hdecr := rebuild_decreases hAO Q R P S hR hSin hQ
  have hgval := rebuilt_singleton_product hAO Q R P S hR hSin hQ
    g hg hgop hgdom u hsingle hlarge
  have hgclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true := by
    intro x hx
    change wval D x (n + g) = true at hx
    rw [hgval x, hP] at hx
    exact projected_singleton_clean G _ u x hx
  have hother : ∀ x, gateVal n D h x = gateVal n C h x := by
    intro x
    exact unchanged_domain_values hAO hD hlen A R hsame hA x (n + h)
      (by omega) (Or.inr (by simpa using hhA))
  have hgedge : ∀ v w, G.Adj v w →
      wval D (pairInput v w) (n + g) = wval C (pairInput v w) (n + g) := by
    intro v w hvw
    rw [hgval, original_singleton_product hAO Q S hSin hQ g hg hgop hgdom u hsingle, hP]
    exact (singleton_neighborhood_projection_pair G _ u v w huB hvw).symm
  have heqedges : ∀ v w, G.Adj v w → circuitFun n D (pairInput v w) =
      circuitFun n C (pairInput v w) := by
    intro v w hvw
    change wval D (pairInput v w) C.output = wval C (pairInput v w) C.output
    by_cases ho : C.output < n + C.gates.length
    · exact outside_region_values hAO hD hlen R g hsame hexit (pairInput v w)
        (hgedge v w hvw) C.output ho hout
    · rw [wval_ge_len C (pairInput v w) (by omega),
        wval_ge_len D (pairInput v w) (by omega)]
  have houtdecr : ∀ x, circuitFun n D x = true → circuitFun n C x = true := by
    intro x hx
    change wval D x C.output = true at hx
    change wval C x C.output = true
    by_cases ho : C.output < n + C.gates.length
    · exact hdecr x C.output ho hx
    · rw [wval_ge_len D x (by omega)] at hx
      cases hx
  have hops : ∀ j < C.gates.length, (gateAt D j).op = (gateAt C j).op := by
    intro j hj
    rw [show gateAt D j = _ from gateAt_rebuild C R (projectedWire P S) hj]
    split_ifs with hr
    · exact repairOr_op (hQ j ((hR j).mp hr).1).1 _ _
    · rfl
  refine ⟨D, hD, rebuild_size C R (projectedWire P S),
    graphFun_preserved_of_edges G hD hfun houtdecr heqedges, hgclean, hother, hops, ?_⟩
  intro j hjdirty
  have hj : j < C.gates.length := by have := hjdirty.2.1; omega
  refine ⟨hops j hj ▸ hjdirty.1, hj, ?_⟩
  obtain ⟨x, hx, hfx⟩ := hjdirty.2.2
  exact ⟨x, hdecr x (n + j) (by omega) hx, hfx⟩

/-- The compiler's semantic invariants imply exactly one remaining dirty AND gate. -/
lemma exactly_one_dirty_of_cleaned {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C D : Circuit} {g h : ℕ}
    (hlen : D.gates.length = C.gates.length)
    (hhop : (gateAt D h).op = (gateAt C h).op)
    (honly : ∀ j, IsDirtyAnd n G C j → j = g ∨ j = h)
    (hhdirty : IsDirtyAnd n G C h)
    (hgclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true)
    (hother : ∀ x, gateVal n D h x = gateVal n C h x)
    (hnew : ∀ j, IsDirtyAnd n G D j → IsDirtyAnd n G C j) :
    ∀ j, IsDirtyAnd n G D j ↔ j = h := by
  intro j
  constructor
  · intro hj
    rcases honly j (hnew j hj) with rfl | rfl
    · obtain ⟨x, hx, hfx⟩ := hj.2.2
      have := hgclean x hx
      rw [hfx] at this
      cases this
    · rfl
  · rintro rfl
    refine ⟨by rw [hhop]; exact hhdirty.1, ?_, ?_⟩
    · rw [hlen]
      exact hhdirty.2.1
    · obtain ⟨x, hx, hfx⟩ := hhdirty.2.2
      exact ⟨x, by rw [hother]; exact hx, hfx⟩


lemma mem_junk_iff_dirty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (j : ℕ) :
    j ∈ junk G C ↔ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨h.2.1, h⟩⟩

/-- A same-size semantic cleaning with one surviving junk contradicts the local
one-junk rung for this graph. -/
lemma same_size_cleaning_contradicts_rung_one {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (rungOne : ∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1)
    {C D : Circuit} (hL : IsLeastAO G C) (hD : IsAO2 n D)
    (hsize : D.size = C.size) (hfun : circuitFun n D = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgclean : ∀ x, gateVal n D g x = true → graphFun G ∅ x = true)
    (hother : ∀ x, gateVal n D h x = gateVal n C h x)
    (hops : ∀ j < C.gates.length, (gateAt D j).op = (gateAt C j).op)
    (hnew : ∀ j, IsDirtyAnd n G D j → IsDirtyAnd n G C j) : False := by
  have hhdirty : IsDirtyAnd n G C h := (mem_junk_iff_dirty G C h).mp (by simp [hJ])
  have honly : ∀ j, IsDirtyAnd n G C j → j = g ∨ j = h := by
    intro j hj
    have hm := (mem_junk_iff_dirty G C j).mpr hj
    simpa [hJ] using hm
  have hlen : D.gates.length = C.gates.length := hsize
  have hexact := exactly_one_dirty_of_cleaned G hlen (hops h hhdirty.2.1)
    honly hhdirty hgclean hother hnew
  have hDJ : junk G D = {h} := by
    ext j
    rw [mem_junk_iff_dirty, Finset.mem_singleton, hexact j]
  have hDL : IsLeastAO G D := by
    refine ⟨hD, hfun, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  apply rungOne D hDL
  rw [hDJ]
  exact Finset.card_singleton h

/-- Under the explicit pure-cone, direct-exit privacy, and preserved-ancestor
hypotheses of the compiler, a least two-junk circuit is excluded by the local
one-junk rung. No general closure of those hypotheses is asserted here. -/
lemma singleton_projection_excludes_two_junk {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (rungOne : ∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C)
    (Q R A : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgdom : ∀ b : Fin 2, opnd C g b < n ∨ opnd C g b - n ∈ Q)
    (u : Fin n) (hsingle : S (opnd C g 0) = {u})
    (hlarge : selected P (S (opnd C g 1)))
    (hP : P = Finset.univ.filter fun t => G.Adj u t)
    (huB : u ∉ S (opnd C g 1))
    (hhA : h ∈ A)
    (hA : ∀ j ∈ A, j ∉ R ∧ ∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ A)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (hout : C.output < n ∨ C.output - n ∉ R) : False := by
  have hgdirty : IsDirtyAnd n G C g := (mem_junk_iff_dirty G C g).mp (by simp [hJ])
  have hhdirty : IsDirtyAnd n G C h := (mem_junk_iff_dirty G C h).mp (by simp [hJ])
  obtain ⟨D, hD, hsize, hfun, hgclean, hother, hops, hnew⟩ :=
    singleton_projection_compiler G hL.1 Q R A P S hR hSin hQ g h
      hgdirty.2.1 hhdirty.2.1 hgdirty.1 hgdom u hsingle hlarge hP huB hhA hA hexit hout hL.2.1
  exact same_size_cleaning_contradicts_rung_one G rungOne hL hD hsize hfun g h hJ
    hgclean hother hops hnew

end Projection



namespace FrontierPrivacy

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma allOnes {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, W n C (fun _ => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [W_input n C _ w hwn]
    · have hk : w - n < C.gates.length := by omega
      have heq : w = n + (w - n) := by omega
      have hmem := gateAt_mem' C (w - n) hk
      have hlen := hAO.2.2 _ hmem
      have hb := hAO.2.1 (w - n) hk
      rcases hAO.1 _ hmem with hop | hop
      · rw [heq]
        apply W_and n C _ _ hk hop
        intro i hi
        have hib := hb i hi
        exact ⟨hib, ih i (by omega) (by omega)⟩
      · cases hlist : (gateAt C (w - n)).inputs with
        | nil => simp [hlist] at hlen
        | cons v vs =>
          have hv : v ∈ (gateAt C (w - n)).inputs := by simp [hlist]
          have hvb := hb v hv
          rw [heq]
          exact W_or n C _ _ hk hop v hv hvb (ih v (by omega) (by omega))

lemma orIn_val {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n}
    (hu : u ∈ orIn n C w) (x : Fin n → Bool) (hxu : x u = true) : W n C x w = true := by
  rcases (orIn_mem n C w u).mp hu with heq | ⟨k, hk, hr, hop, hin⟩
  · rw [← heq, W_input n C x u.val u.isLt]
    exact hxu
  · have hkv : W n C x (n + k) = true := by
      apply W_or n C x k hk hop u.val hin (by have := u.isLt; omega)
      rw [W_input n C x u.val u.isLt]
      exact hxu
    exact reach_up n C x w k hr hkv

lemma no_clean_and_filter {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h j a b : ℕ} {f : (Fin n → Bool) → Bool}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hinputs : (gateAt C j).inputs = [a,b] ∨ (gateAt C j).inputs = [b,a])
    (hdom : ∀ x, f x = true → W n C x a = true)
    (hraw : ∀ u : Fin n, ∃ x, f x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, f x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, f x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false) :
    ¬ BelowF G C j := by
  intro hclean
  have hb : b ∈ (gateAt C j).inputs := by
    rcases hinputs with hlist | hlist <;> simp [hlist]
  have hback := hAO.2.1 j hj
  have hbval := allOnes hAO b (by have := hback b hb; omega)
  have hwit : ∃ x, f x = true ∧ W n C x b = true ∧ graphFun G ∅ x = false := by
    rcases down n C (fun _ => true) (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) b hbval with
      ⟨u, hu, _⟩ | ⟨k, hk, hr, hopk, _⟩
    · obtain ⟨x, hfx, hxu, hneg⟩ := hraw u
      exact ⟨x, hfx, orIn_val hu x hxu, hneg⟩
    · have hnotbelow : ¬ BelowF G C k := by
        intro hkclean
        exact hTF k hk j hj hopk hkclean hop (reach_cone n C j hj b hb (hback b hb) k hr)
      have hkJ : k ∈ junk G C := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_range.mpr hk, hopk, hk, ?_⟩
        unfold BelowF at hnotbelow
        push Not at hnotbelow
        obtain ⟨x, hx, hf⟩ := hnotbelow
        exact ⟨x, hx, by simpa using hf⟩
      rcases hJ k hkJ with rfl | rfl
      · obtain ⟨x, hfx, hgv, hneg⟩ := hg
        exact ⟨x, hfx, reach_up n C x b _ hr hgv, hneg⟩
      · obtain ⟨x, hfx, hhv, hneg⟩ := hh
        exact ⟨x, hfx, reach_up n C x b _ hr hhv, hneg⟩
  obtain ⟨x, hfx, hbx, hneg⟩ := hwit
  have hjx : gateVal n C j x = true := by
    apply W_and n C x j hj hop
    intro i hi
    refine ⟨hback i hi, ?_⟩
    have hi2 : i = a ∨ i = b := by
      rcases hinputs with hlist | hlist
      · simpa only [hlist, List.mem_cons, List.not_mem_nil, or_false] using hi
      · have hi3 : i = b ∨ i = a := by
          simpa only [hlist, List.mem_cons, List.not_mem_nil, or_false] using hi
        exact hi3.symm
    rcases hi2 with rfl | rfl
    · exact hdom x hfx
    · exact hbx
  have := hclean x hjx
  rw [hneg] at this
  exact Bool.false_ne_true this

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem' C j hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma and_reader_is_junk_of_witnesses {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h p j w : ℕ}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hw : w ∈ (gateAt C j).inputs) (hreach : OrReaches n C w p)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false) :
    j = g ∨ j = h := by
  have hinputs := gate_inputs_eq hAO hj
  have hdom : ∀ x, gateVal n C p x = true → W n C x w = true := by
    intro x hx
    exact reach_up n C x w p hreach hx
  have hnotbelow : ¬ BelowF G C j := by
    have hw2 : w = opnd C j 0 ∨ w = opnd C j 1 := by
      simpa only [hinputs, List.mem_cons, List.not_mem_nil, or_false] using hw
    rcases hw2 with rfl | rfl
    · exact no_clean_and_filter hAO hTF hJ hj hop (Or.inl hinputs) hdom hraw hg hh
    · exact no_clean_and_filter hAO hTF hJ hj hop (Or.inr hinputs) hdom hraw hg hh
  apply hJ j
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr hj, hop, hj, ?_⟩
  unfold BelowF at hnotbelow
  push Not at hnotbelow
  obtain ⟨x, hx, hf⟩ := hnotbelow
  exact ⟨x, hx, by simpa using hf⟩


lemma gate_op_cases {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  exact hAO.1 _ (gateAt_mem' C j hj)

lemma read_index_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i j : ℕ} (hj : j < C.gates.length)
    (hread : n + i ∈ (gateAt C j).inputs) : i < j := by
  have h := hAO.2.1 j hj (n + i) hread
  omega

lemma and_frontier_not_below_of_witnesses {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    {g h p j w : ℕ}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (hw : w ∈ (gateAt C j).inputs) (hreach : OrReaches n C w p)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false) :
    ¬ BelowF G C j := by
  have hinputs := gate_inputs_eq hAO hj
  have hdom : ∀ x, gateVal n C p x = true → W n C x w = true := by
    intro x hx
    exact reach_up n C x w p hreach hx
  have hw2 : w = opnd C j 0 ∨ w = opnd C j 1 := by
    simpa only [hinputs, List.mem_cons, List.not_mem_nil, or_false] using hw
  rcases hw2 with rfl | rfl
  · exact no_clean_and_filter hAO hTF hJ hj hop (Or.inl hinputs) hdom hraw hg hh
  · exact no_clean_and_filter hAO hTF hJ hj hop (Or.inr hinputs) hdom hraw hg hh

lemma dirty_root_no_output_orReach {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} {p : ℕ}
    (hcompute : circuitFun n C = graphFun G ∅)
    (hdirty : ∃ x, gateVal n C p x = true ∧ graphFun G ∅ x = false) :
    ¬ OrReaches n C C.output p := by
  intro hreach
  obtain ⟨x, hpx, hneg⟩ := hdirty
  have hv := reach_up n C x C.output p hreach hpx
  change circuitFun n C x = true at hv
  rw [hcompute, hneg] at hv
  exact Bool.false_ne_true hv

lemma dirty_frontier_eventually_junk {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : circuitFun n C = graphFun G ∅) {g h p i : ℕ}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hlive : ∀ q < C.gates.length,
      C.output = n + q ∨ ∃ j < C.gates.length, n + q ∈ (gateAt C j).inputs)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hi : i < C.gates.length) (hPi : OrReaches n C (n + i) p) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ (j = g ∨ j = h) ∧
      ∃ w ∈ (gateAt C j).inputs, OrReaches n C w i ∧ OrReaches n C w p := by
  have hout : ¬ OrReaches n C C.output p :=
    dirty_root_no_output_orReach hcompute (by
      obtain ⟨x, hpx, _, hneg⟩ := hg
      exact ⟨x, hpx, hneg⟩)
  have aux : ∀ d q, C.gates.length - q = d → q < C.gates.length →
      OrReaches n C (n + q) p → OrReaches n C (n + q) i →
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ (j = g ∨ j = h) ∧
        ∃ w ∈ (gateAt C j).inputs, OrReaches n C w i ∧ OrReaches n C w p := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro q hqd hq hqp hqi
      rcases hlive q hq with hqo | ⟨j, hj, hread⟩
      · exact (hout (hqo ▸ hqp)).elim
      · have hqj := read_index_lt hAO hj hread
        rcases gate_op_cases hAO hj with hand | hor
        · exact ⟨j, hj, hand,
            and_reader_is_junk_of_witnesses hAO hTF hJ hj hand hread hqp hraw hg hh,
            n + q, hread, hqi, hqp⟩
        · apply ih (C.gates.length - j) (by omega) j rfl hj
          · exact orReach_trans n C j hj hor (n + q) hread (by omega) p hqp
          · exact orReach_trans n C j hj hor (n + q) hread (by omega) i hqi
  exact aux (C.gates.length - i) i rfl hi hPi (orReach_self n C i hi)

lemma dirty_frontier_eventually_target {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : circuitFun n C = graphFun G ∅) {g h p i : ℕ}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hlive : ∀ q < C.gates.length,
      C.output = n + q ∨ ∃ j < C.gates.length, n + q ∈ (gateAt C j).inputs)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hnoh : ∀ w ∈ (gateAt C h).inputs, ¬ OrReaches n C w p)
    (hi : i < C.gates.length) (hPi : OrReaches n C (n + i) p) :
    ∃ w ∈ (gateAt C g).inputs, OrReaches n C w i ∧ OrReaches n C w p := by
  obtain ⟨j, _, _, hj, w, hw, hwi, hwp⟩ :=
    dirty_frontier_eventually_junk hAO hTF hcompute hJ hlive hraw hg hh hi hPi
  rcases hj with rfl | rfl
  · exact ⟨w, hw, hwi, hwp⟩
  · exact (hnoh w hw hwp).elim

lemma sole_reader_of_frontier_exclusions {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : circuitFun n C = graphFun G ∅) {g h p : ℕ}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hlive : ∀ q < C.gates.length,
      C.output = n + q ∨ ∃ j < C.gates.length, n + q ∈ (gateAt C j).inputs)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hp : p < C.gates.length) (hgN : g < C.gates.length) (c : Fin 2)
    (hroot : opnd C g c = n + p)
    (hother : ¬ OrReaches n C (opnd C g (1 - c)) p)
    (hnoh : ∀ w ∈ (gateAt C h).inputs, ¬ OrReaches n C w p) :
    readers n C p = {g} := by
  have hself := orReach_self n C p hp
  have hpg : n + p ∈ (gateAt C g).inputs := by
    rw [← hroot, gate_inputs_eq hAO hgN]
    fin_cases c <;> simp
  apply Finset.ext
  intro j
  simp only [readers, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hread⟩
    rcases gate_op_cases hAO hj with hand | hor
    · rcases and_reader_is_junk_of_witnesses hAO hTF hJ hj hand hread hself hraw hg hh with rfl | rfl
      · rfl
      · exact (hnoh (n + p) hread hself).elim
    · have hpj := read_index_lt hAO hj hread
      have hPj := orReach_trans n C j hj hor (n + p) hread (by omega) p hself
      obtain ⟨w, hw, hwj, hwp⟩ :=
        dirty_frontier_eventually_target hAO hTF hcompute hJ hlive hraw hg hh hnoh hj hPj
      have hw01 : w = opnd C g 0 ∨ w = opnd C g 1 := by
        simpa only [gate_inputs_eq hAO hgN, List.mem_cons, List.not_mem_nil, or_false] using hw
      have hwc : w = opnd C g c ∨ w = opnd C g (1 - c) := by
        fin_cases c
        · simpa using hw01
        · simpa using hw01.symm
      rcases hwc with hwc | hwc
      · rw [hwc, hroot] at hwj
        have hjp := orSets_cone n C p hp j (by simpa using hwj.2)
        rcases hjp with hjp | hjp
        · omega
        · have hlt := inCone_lt n C p j hjp
          omega
      · exact (hother (hwc ▸ hwp)).elim
  · rintro rfl
    exact ⟨hgN, hpg⟩

lemma not_orReach_of_filterable_wire {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} {p w : ℕ}
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hfilter : ∃ v : Fin n, ∀ x,
      W n C x w = true → x v = true → graphFun G ∅ x = true) :
    ¬ OrReaches n C w p := by
  intro hreach
  obtain ⟨v, hfilter⟩ := hfilter
  obtain ⟨x, hpx, hxv, hneg⟩ := hraw v
  have hw := reach_up n C x w p hreach hpx
  have hf := hfilter x hw hxv
  rw [hneg] at hf
  exact Bool.false_ne_true hf

lemma dirty_frontier_eventually_target_of_filterable_operands
    {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : circuitFun n C = graphFun G ∅) {g h p i : ℕ}
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hlive : ∀ q < C.gates.length,
      C.output = n + q ∨ ∃ j < C.gates.length, n + q ∈ (gateAt C j).inputs)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hfilter : ∀ w ∈ (gateAt C h).inputs, ∃ v : Fin n, ∀ x,
      W n C x w = true → x v = true → graphFun G ∅ x = true)
    (hi : i < C.gates.length) (hPi : OrReaches n C (n + i) p) :
    ∃ w ∈ (gateAt C g).inputs, OrReaches n C w i ∧ OrReaches n C w p := by
  apply dirty_frontier_eventually_target hAO hTF hcompute hJ hlive hraw hg hh
    (fun w hw => not_orReach_of_filterable_wire hraw (hfilter w hw)) hi hPi

end FrontierPrivacy


-- AncestorBridge extension begins here.
namespace ProjectionAncestor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.Projection

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

/-- The direct-exit contract applies to any input-list member, not just a named slot. -/
lemma exit_input_not_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R : Finset ℕ) (g : ℕ)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    {j w : ℕ} (hj : j < C.gates.length) (hjR : j ∉ R) (hjg : j ≠ g)
    (hw : w ∈ (gateAt C j).inputs) (hnw : n ≤ w) : w - n ∉ R := by
  rw [gate_inputs_eq hAO hj] at hw
  simp at hw
  rcases hw with rfl | rfl
  · rcases hexit j hj hjR hjg 0 with hraw | hnot
    · omega
    · exact hnot
  · rcases hexit j hj hjR hjg 1 with hraw | hnot
    · omega
    · exact hnot

/-- An ancestor in the changed region must cross its designated exit before reaching
an outside gate. The target's exclusion from R is essential. -/
lemma region_ancestor_forces_frontier {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R : Finset ℕ) (g : ℕ)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    {i j : ℕ} (hi : i ∈ R) (hjR : j ∉ R) (hij : InCone n C i j) :
    g = j ∨ InCone n C g j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hjg : j = g
    · exact Or.inl hjg.symm
    · have hj := inCone_lt_len hij
      obtain ⟨w, hw, hnw, hwj, hsub⟩ := (inCone_iff hj).mp hij
      have hwR := exit_input_not_mem hAO R g hexit hj hjR hjg hw hnw
      rcases hsub with hsame | hsub
      · exact False.elim (hwR (hsame ▸ hi))
      · have hforce := ih (w - n) (by omega) hwR hsub
        right
        exact (inCone_iff hj).mpr ⟨w, hw, hnw, hwj, hforce⟩

def ancestorDomain (n : ℕ) (C : Circuit) (h : ℕ) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun j => j = h ∨ InCone n C j h

lemma mem_ancestorDomain {n : ℕ} {C : Circuit} {h j : ℕ} :
    j ∈ ancestorDomain n C h ↔ j < C.gates.length ∧ (j = h ∨ InCone n C j h) := by
  simp only [ancestorDomain, Finset.mem_filter, Finset.mem_range]

lemma ancestorDomain_contains {n : ℕ} {C : Circuit} {h : ℕ}
    (hh : h < C.gates.length) : h ∈ ancestorDomain n C h :=
  mem_ancestorDomain.mpr ⟨hh, Or.inl rfl⟩

lemma ancestorDomain_hereditary {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (h : ℕ) : ∀ j ∈ ancestorDomain n C h, ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∈ ancestorDomain n C h := by
  intro j hj b
  obtain ⟨hjlen, hjanc⟩ := mem_ancestorDomain.mp hj
  by_cases hraw : opnd C j b < n
  · exact Or.inl hraw
  · right
    have hback := opnd_lt hAO hjlen b
    have hchild : InCone n C (opnd C j b - n) j :=
      (inCone_iff hjlen).mpr ⟨opnd C j b, opnd_mem hAO hjlen b, by omega, hback, Or.inl rfl⟩
    apply mem_ancestorDomain.mpr
    refine ⟨by omega, Or.inr ?_⟩
    rcases hjanc with rfl | hjanc
    · exact hchild
    · exact inCone_trans hchild hjanc

lemma ancestorDomain_disjoint_region {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R : Finset ℕ) (g h : ℕ)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (hhR : h ∉ R) (hgh : g ≠ h) (hnot : ¬ InCone n C g h) :
    ∀ j ∈ ancestorDomain n C h, j ∉ R := by
  intro j hj hjR
  obtain ⟨_, hjanc⟩ := mem_ancestorDomain.mp hj
  rcases hjanc with rfl | hjanc
  · exact hhR hjR
  · rcases region_ancestor_forces_frontier hAO R g hexit hjR hhR hjanc with hEq | hCone
    · exact hgh hEq
    · exact hnot hCone

lemma exists_unchanged_ancestor_domain {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R : Finset ℕ) (g h : ℕ) (hh : h < C.gates.length)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (hhR : h ∉ R) (hgh : g ≠ h) (hnot : ¬ InCone n C g h) :
    ∃ A : Finset ℕ, h ∈ A ∧
      ∀ j ∈ A, j ∉ R ∧ ∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ A := by
  refine ⟨ancestorDomain n C h, ancestorDomain_contains hh, ?_⟩
  intro j hj
  exact ⟨ancestorDomain_disjoint_region hAO R g h hexit hhR hgh hnot j hj,
    ancestorDomain_hereditary hAO h j hj⟩

lemma exists_unchanged_ancestor_domain_of_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (R : Finset ℕ) (g h : ℕ) (hh : h < C.gates.length)
    (hRor : ∀ j ∈ R, (gateAt C j).op = GateOp.or)
    (hhand : (gateAt C h).op = GateOp.and)
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (hgh : g ≠ h) (hnot : ¬ InCone n C g h) :
    ∃ A : Finset ℕ, h ∈ A ∧
      ∀ j ∈ A, j ∉ R ∧ ∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ A := by
  apply exists_unchanged_ancestor_domain hAO R g h hh hexit _ hgh hnot
  intro hhR
  have hor := hRor h hhR
  rw [hhand] at hor
  cases hor


/-- The independent-gate form of the singleton exclusion: the unchanged ancestor
domain is derived from direct-exit privacy and nondependence, rather than assumed. -/
lemma singleton_projection_excludes_two_junk_of_independent {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rungOne : ∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C)
    (Q R : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (hgdom : ∀ b : Fin 2, opnd C g b < n ∨ opnd C g b - n ∈ Q)
    (u : Fin n) (hsingle : S (opnd C g 0) = {u})
    (hlarge : selected P (S (opnd C g 1)))
    (hP : P = Finset.univ.filter fun t => G.Adj u t)
    (huB : u ∉ S (opnd C g 1))
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R)
    (hout : C.output < n ∨ C.output - n ∉ R) : False := by
  have hhdirty : IsDirtyAnd n G C h := (mem_junk_iff_dirty G C h).mp (by simp [hJ])
  have hRor : ∀ j ∈ R, (gateAt C j).op = GateOp.or :=
    fun j hj => (hQ j ((hR j).mp hj).1).1
  obtain ⟨A, hhA, hA⟩ := exists_unchanged_ancestor_domain_of_and hL.1 R g h hhdirty.2.1
    hRor hhdirty.1 hexit hgh hind
  exact singleton_projection_excludes_two_junk G rungOne hL Q R A P S hR hSin hQ
    g h hJ hgdom u hsingle hlarge hP huB hhA hA hexit hout

end ProjectionAncestor


-- OutputBridge extension begins here.
namespace ProjectionOutput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo
  PEqualNP.Outside.L_meta_5012.Projection PEqualNP.Outside.L_meta_5012.ProjectionAncestor

lemma graphFun_singleton_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun t => decide (t = v)) = false := by
  rw [graphFun, Bool.or_eq_false_iff]
  constructor
  · simp
  · rw [decide_eq_false_iff_not]
    rintro ⟨a, b, hab, ha, hb⟩
    simp only [decide_eq_true_eq] at ha hb
    subst a
    subst b
    exact G.loopless.irrefl v hab

lemma output_valid_of_graph_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (hfun : circuitFun n C = graphFun G ∅)
    {v w : Fin n} (hvw : G.Adj v w) : C.output < n + C.gates.length := by
  by_contra hout
  have htrue : circuitFun n C (pairInput v w) = true := by
    rw [hfun]
    unfold graphFun
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
    exact Or.inr ⟨v, w, hvw, by simp [pairInput], by simp [pairInput]⟩
  change wval C (pairInput v w) C.output = true at htrue
  rw [wval_ge_len C (pairInput v w) (by omega)] at htrue
  cases htrue

/-- A valid output computing a graph function cannot be a selected pure OR gate:
its nonempty raw support would accept a singleton input. -/
lemma output_outside_selected_region {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C)
    (Q R : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (hfun : circuitFun n C = graphFun G ∅) (hout : C.output < n + C.gates.length) :
    C.output < n ∨ C.output - n ∉ R := by
  by_cases hraw : C.output < n
  · exact Or.inl hraw
  · right
    intro hmem
    let j := C.output - n
    have hj : j < C.gates.length := by dsimp [j]; omega
    have houtj : n + j = C.output := by dsimp [j]; omega
    have hq := ((hR j).mp hmem).1
    have hselected := ((hR j).mp hmem).2
    obtain ⟨v, hv⟩ := selected_projected_nonempty hselected
    have hp := pure_cone_values hAO Q S hSin hQ (fun t => decide (t = v))
      (n + j) (by omega) (Or.inr (by simpa using hq))
    have htrue : circuitFun n C (fun t => decide (t = v)) = true := by
      change wval C (fun t => decide (t = v)) C.output = true
      rw [← houtj, hp]
      simp only [setOr, decide_eq_true_eq]
      exact ⟨v, (Finset.mem_inter.mp hv).1, by simp⟩
    rw [hfun, graphFun_singleton_false G v] at htrue
    cases htrue

/-- A singleton projection with a pure OR domain and full direct-exit privacy is
incompatible with a least independent two-junk circuit under the local one-junk
rung. The ancestor domain and output exclusion are both derived. -/
lemma singleton_projection_excludes_independent_two_junk {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (rungOne : ∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C)
    (Q R : Finset ℕ) (P : Finset (Fin n)) (S : ℕ → Finset (Fin n))
    (hR : ∀ j, j ∈ R ↔ j ∈ Q ∧ selected P (S (n + j)))
    (hSin : ∀ w (hw : w < n), S w = {⟨w, hw⟩})
    (hQ : ∀ j ∈ Q, (gateAt C j).op = GateOp.or ∧
      S (n + j) = S (opnd C j 0) ∪ S (opnd C j 1) ∧
      (∀ b : Fin 2, opnd C j b < n ∨ opnd C j b - n ∈ Q))
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (hgdom : ∀ b : Fin 2, opnd C g b < n ∨ opnd C g b - n ∈ Q)
    (u : Fin n) (hsingle : S (opnd C g 0) = {u})
    (hlarge : selected P (S (opnd C g 1)))
    (hP : P = Finset.univ.filter fun t => G.Adj u t)
    (huB : u ∉ S (opnd C g 1))
    (hexit : ∀ j < C.gates.length, j ∉ R → j ≠ g → ∀ b : Fin 2,
      opnd C j b < n ∨ opnd C j b - n ∉ R) : False := by
  obtain ⟨v, hv⟩ := selected_projected_nonempty hlarge
  have huv : G.Adj u v := by
    have hmem := (Finset.mem_inter.mp hv).2
    simpa [hP] using hmem
  have houtvalid := output_valid_of_graph_edge G hL.2.1 huv
  have hout := output_outside_selected_region G hL.1 Q R P S hR hSin hQ hL.2.1 houtvalid
  exact singleton_projection_excludes_two_junk_of_independent G rungOne hL Q R P S
    hR hSin hQ g h hJ hgh hind hgdom u hsingle hlarge hP huB hexit hout

end ProjectionOutput

end PEqualNP.Outside.L_meta_5012
