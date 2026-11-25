import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def setOr {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ A, x a = true)

def setProduct {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  setOr A x && setOr B x

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun
  simp

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma setOr_pair {n : ℕ} (A : Finset (Fin n)) (u v : Fin n) :
    setOr A (pairInput u v) = true ↔ u ∈ A ∨ v ∈ A := by
  simp only [setOr, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, ha, rfl | rfl⟩
    · exact Or.inl ha
    · exact Or.inr ha
  · rintro (hu | hv)
    · exact ⟨u, hu, Or.inl rfl⟩
    · exact ⟨v, hv, Or.inr rfl⟩

lemma mutual_intersection_adj {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A B C D : Finset (Fin n)}
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true)
    {u v : Fin n} (hu : u ∈ A ∩ C) (hv : v ∈ B ∩ D) : G.Adj u v := by
  apply (graphFun_pair_iff u v).mp
  apply hclean (pairInput u v)
  · simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inl (Finset.mem_inter.mp hu).1, Or.inr (Finset.mem_inter.mp hv).1⟩
  · simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inl (Finset.mem_inter.mp hu).2, Or.inr (Finset.mem_inter.mp hv).2⟩

lemma biclique_one_side_small {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A B : Finset (Fin n)}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b) : A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases ha : A.card ≤ 1
  · exact Or.inl ha
  · right
    obtain ⟨a, haA, c, hcA, hac⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    have hsub : B ⊆ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hAB a haA b hb, hAB c hcA b hb⟩
    exact (Finset.card_le_card hsub).trans (h4 a c hac)

lemma mutual_intersection_is_star {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A B C D : Finset (Fin n)}
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    (A ∩ C).card ≤ 1 ∨ (B ∩ D).card ≤ 1 := by
  exact biclique_one_side_small h4 fun _ hu _ hv => mutual_intersection_adj hclean hu hv

lemma mutual_common_vertex_filter {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A B C D : Finset (Fin n)}
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true)
    {u : Fin n} (hu : u ∈ A ∩ C) :
    (∀ b ∈ B, G.Adj u b) ∨ (∀ d ∈ D, G.Adj u d) := by
  by_contra h
  push Not at h
  obtain ⟨⟨b, hb, hub⟩, ⟨d, hd, hud⟩⟩ := h
  let x : Fin n → Bool := fun v => decide (v = u ∨ v = b ∨ v = d)
  have hxu : x u = true := by simp [x]
  have hxb : x b = true := by simp [x]
  have hxd : x d = true := by simp [x]
  have hf := hclean x
    (by simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq]
        exact ⟨⟨u, (Finset.mem_inter.mp hu).1, hxu⟩, ⟨b, hb, hxb⟩⟩)
    (by simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq]
        exact ⟨⟨u, (Finset.mem_inter.mp hu).2, hxu⟩, ⟨d, hd, hxd⟩⟩)
  obtain ⟨v, w, hvw, hv, hw⟩ := (graphFun_iff x).mp hf
  simp only [x, decide_eq_true_eq] at hv hw
  rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
  · exact G.loopless.irrefl _ hvw
  · exact hub hvw
  · exact hud hvw
  · exact hub hvw.symm
  · exact G.loopless.irrefl _ hvw
  · exact hBD _ hb _ hd hvw
  · exact hud hvw.symm
  · exact hBD _ hb _ hd hvw.symm
  · exact G.loopless.irrefl _ hvw

def universalTo {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∀ b ∈ B, G.Adj u b

lemma universalTo_card_le_one {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {B : Finset (Fin n)}
    (hB : 2 ≤ B.card) : (universalTo G B).card ≤ 1 := by
  have h := biclique_one_side_small h4 (A := universalTo G B) (B := B) (by
    intro a ha b hb
    exact (Finset.mem_filter.mp ha).2 b hb)
  omega

lemma mutual_common_card_le_two {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A B C D : Finset (Fin n)}
    (hB : 2 ≤ B.card) (hD : 2 ≤ D.card)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    (A ∩ C).card ≤ 2 := by
  have hsub : A ∩ C ⊆ universalTo G B ∪ universalTo G D := by
    intro u hu
    rcases mutual_common_vertex_filter hBD hclean hu with h | h
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (universalTo G B) (universalTo G D)
  have h3 := universalTo_card_le_one h4 hB
  have h5 := universalTo_card_le_one h4 hD
  omega

lemma setProduct_comm {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    setProduct A B x = setProduct B A x := by
  exact Bool.and_comm _ _

lemma mutual_intersection_edge_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A B C D : Finset (Fin n)}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (hAC : ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    ((A ∩ C) ×ˢ (B ∩ D)).card ≤ 2 := by
  have hleft := mutual_common_card_le_two h4 hB hD hBD hclean
  have hright := mutual_common_card_le_two h4 hA hC hAC (A := B) (C := D) (by
    intro x hx hy
    exact hclean x (by simpa only [setProduct_comm B A] using hx)
      (by simpa only [setProduct_comm D C] using hy))
  rw [Finset.card_product]
  rcases mutual_intersection_is_star h4 hclean with h | h
  · calc
      (A ∩ C).card * (B ∩ D).card ≤ 1 * 2 := Nat.mul_le_mul h hright
      _ = 2 := rfl
  · calc
      (A ∩ C).card * (B ∩ D).card ≤ 2 * 1 := Nat.mul_le_mul hleft h
      _ = 2 := rfl

lemma bipartite_same_color_nonadj {n : ℕ} {G : SimpleGraph (Fin n)}
    (s : Fin n → Bool) (hs : ∀ u v, G.Adj u v → s u ≠ s v)
    {u v : Fin n} (huv : s u = s v) : ¬ G.Adj u v := by
  intro h
  exact hs u v h huv

lemma mutual_intersection_edge_bound_bipartite {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hs : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    {A B C D : Finset (Fin n)}
    (hA : 2 ≤ A.card) (hB : 2 ≤ B.card) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (hAs : ∀ a ∈ A, s a = false) (hBs : ∀ b ∈ B, s b = true)
    (hCs : ∀ c ∈ C, s c = false) (hDs : ∀ d ∈ D, s d = true)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    (((A ∩ C) ×ˢ (B ∩ D)).image fun p => s(p.1, p.2)).card ≤ 2 := by
  apply (Finset.card_image_le).trans
  apply mutual_intersection_edge_bound h4 hA hB hC hD
  · intro a ha c hc
    exact bipartite_same_color_nonadj s hs ((hAs a ha).trans (hCs c hc).symm)
  · intro b hb d hd
    exact bipartite_same_color_nonadj s hs ((hBs b hb).trans (hDs d hd).symm)
  · exact hclean

lemma mutual_pair_trace {n : ℕ} {A B C D : Finset (Fin n)}
    (s : Fin n → Bool)
    (hAs : ∀ a ∈ A, s a = false) (hBs : ∀ b ∈ B, s b = true)
    (hCs : ∀ c ∈ C, s c = false) (hDs : ∀ d ∈ D, s d = true)
    (u v : Fin n) :
    (setProduct A B (pairInput u v) = true ∧
      setProduct C D (pairInput u v) = true) ↔
    (u ∈ A ∩ C ∧ v ∈ B ∩ D) ∨ (v ∈ A ∩ C ∧ u ∈ B ∩ D) := by
  have hABu : ¬ (u ∈ A ∧ u ∈ B) := by
    rintro ⟨ha, hb⟩
    have := (hAs u ha).symm.trans (hBs u hb)
    contradiction
  have hABv : ¬ (v ∈ A ∧ v ∈ B) := by
    rintro ⟨ha, hb⟩
    have := (hAs v ha).symm.trans (hBs v hb)
    contradiction
  have hCDu : ¬ (u ∈ C ∧ u ∈ D) := by
    rintro ⟨hc, hd⟩
    have := (hCs u hc).symm.trans (hDs u hd)
    contradiction
  have hCDv : ¬ (v ∈ C ∧ v ∈ D) := by
    rintro ⟨hc, hd⟩
    have := (hCs v hc).symm.trans (hDs v hd)
    contradiction
  have hADu : ¬ (u ∈ A ∧ u ∈ D) := by
    rintro ⟨ha, hd⟩
    have := (hAs u ha).symm.trans (hDs u hd)
    contradiction
  have hADv : ¬ (v ∈ A ∧ v ∈ D) := by
    rintro ⟨ha, hd⟩
    have := (hAs v ha).symm.trans (hDs v hd)
    contradiction
  simp only [setProduct, Bool.and_eq_true, setOr_pair, Finset.mem_inter]
  tauto

namespace OneFlag

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma common_neighbor_unique {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {u z t v : Fin n}
    (huz : u ≠ z) (hut : G.Adj u t) (hzt : G.Adj z t)
    (huv : G.Adj u v) (hzv : G.Adj z v) : v = t := by
  apply Finset.card_le_one.mp (h4 u z huz)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨huv, hzv⟩⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hut, hzt⟩⟩

lemma no_common_neighbor_of_bad_member {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A : Finset (Fin n)}
    {u z t a : Fin n} (hu : u ∈ A) (hz : z ∈ A) (ha : a ∈ A)
    (huz : u ≠ z) (hut : G.Adj u t) (hzt : G.Adj z t)
    (hat : ¬ G.Adj a t) : ¬ ∃ v : Fin n, ∀ w ∈ A, G.Adj w v := by
  rintro ⟨v, hv⟩
  have hvt := common_neighbor_unique h4 huz hut hzt (hv u hu) (hv z hz)
  exact hat (hvt ▸ hv a ha)

lemma exists_member_ne_of_card {n : ℕ} {A : Finset (Fin n)}
    (hA : 2 ≤ A.card) (z : Fin n) : ∃ a ∈ A, a ≠ z := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  by_cases haz : a = z
  · exact ⟨b, hb, fun hbz => hab (haz.trans hbz.symm)⟩
  · exact ⟨a, ha, haz⟩

lemma one_flag_raw_side_bad_witness {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    {A C D : Finset (Fin n)} {u z t : Fin n}
    (hu : u ∈ A) (huz : u ≠ z) (hut : G.Adj u t) (hzt : G.Adj z t)
    (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (hCt : ∀ c ∈ C, G.Adj c t) (hzD : ∀ d ∈ D, G.Adj z d) :
    ∃ x : Fin n → Bool, setOr A x = true ∧ setProduct C D x = true ∧
      graphFun G ∅ x = false := by
  obtain ⟨c, hc, hcz⟩ := exists_member_ne_of_card hC z
  obtain ⟨d, hd, hdt⟩ := exists_member_ne_of_card hD t
  have hct := hCt c hc
  have hzd := hzD d hd
  have hud : ¬ G.Adj u d := by
    intro hud
    exact hdt (common_neighbor_unique h4 huz hut hzt hud hzd)
  have hcd : ¬ G.Adj c d := by
    intro hcd
    exact hdt (common_neighbor_unique h4 hcz hct hzt hcd hzd)
  have huc : ¬ G.Adj u c := by
    intro huc
    have h1 := hbip u t hut
    have h2 := hbip c t hct
    have h3 := hbip u c huc
    cases hsu : s u <;> cases hsc : s c <;> cases hst : s t <;> simp_all
  let x : Fin n → Bool := fun v => decide (v = u ∨ v = c ∨ v = d)
  have hxu : x u = true := by simp [x]
  have hxc : x c = true := by simp [x]
  have hxd : x d = true := by simp [x]
  refine ⟨x, ?_, ?_, ?_⟩
  · simp only [setOr, decide_eq_true_eq]
    exact ⟨u, hu, hxu⟩
  · simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq]
    exact ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩
  · apply Bool.eq_false_iff.mpr
    intro hf
    obtain ⟨v, w, hvw, hv, hw⟩ := (graphFun_iff x).mp hf
    simp only [x, decide_eq_true_eq] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hvw
    · exact huc hvw
    · exact hud hvw
    · exact huc hvw.symm
    · exact G.loopless.irrefl _ hvw
    · exact hcd hvw
    · exact hud hvw.symm
    · exact hcd hvw.symm
    · exact G.loopless.irrefl _ hvw

end OneFlag

end PEqualNP.Outside.L_meta_5012
