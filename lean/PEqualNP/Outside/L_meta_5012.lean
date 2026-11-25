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

lemma two_center_restriction_dirty {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {B : Finset (Fin n)}
    {u z t : Fin n} (huz : u ≠ z) (hut : G.Adj u t) (hzt : G.Adj z t)
    (hB : 2 ≤ B.card) (huB : ∀ b ∈ B, G.Adj u b) :
    ∃ x : Fin n → Bool, setProduct {u, z} B x = true ∧ graphFun G ∅ x = false := by
  obtain ⟨b, hb, hbt⟩ := exists_member_ne_of_card hB t
  have hzb : ¬ G.Adj z b := by
    intro hzb
    exact hbt (common_neighbor_unique h4 huz hut hzt (huB b hb) hzb)
  refine ⟨pairInput z b, ?_, ?_⟩
  · simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inl (by simp), Or.inr hb⟩
  · apply Bool.eq_false_iff.mpr
    intro hF
    exact hzb ((graphFun_pair_iff z b).mp hF)

lemma two_center_restriction_le {n : ℕ} {A B : Finset (Fin n)}
    {u z : Fin n} (hu : u ∈ A) (hz : z ∈ A) :
    ∀ x : Fin n → Bool, setProduct {u, z} B x = true → setProduct A B x = true := by
  intro x hx
  simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq] at hx ⊢
  obtain ⟨⟨a, ha, hxa⟩, hB⟩ := hx
  refine ⟨⟨a, ?_, hxa⟩, hB⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact hu
  · exact hz

lemma raw_product_bad_witness_of_no_common_neighbor {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {A C D : Finset (Fin n)}
    (hA : ¬ ∃ v : Fin n, ∀ a ∈ A, G.Adj a v) {c d : Fin n}
    (hc : c ∈ C) (hd : d ∈ D) (hcd : ¬ G.Adj c d)
    (hAc : ∀ a ∈ A, ¬ G.Adj a c) :
    ∃ x : Fin n → Bool, setOr A x = true ∧ setProduct C D x = true ∧
      graphFun G ∅ x = false := by
  have hex : ∃ a ∈ A, ¬ G.Adj a d := by
    by_contra h
    apply hA
    refine ⟨d, ?_⟩
    intro a ha
    by_contra had
    exact h ⟨a, ha, had⟩
  obtain ⟨a, ha, had⟩ := hex
  have hac := hAc a ha
  let x : Fin n → Bool := fun v => decide (v = a ∨ v = c ∨ v = d)
  have hxa : x a = true := by simp [x]
  have hxc : x c = true := by simp [x]
  have hxd : x d = true := by simp [x]
  refine ⟨x, ?_, ?_, ?_⟩
  · simp only [setOr, decide_eq_true_eq]
    exact ⟨a, ha, hxa⟩
  · simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq]
    exact ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩
  · apply Bool.eq_false_iff.mpr
    intro hf
    obtain ⟨v, w, hvw, hv, hw⟩ := (graphFun_iff x).mp hf
    simp only [x, decide_eq_true_eq] at hv hw
    rcases hv with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hvw
    · exact hac hvw
    · exact had hvw
    · exact hac hvw.symm
    · exact G.loopless.irrefl _ hvw
    · exact hcd hvw
    · exact had hvw.symm
    · exact hcd hvw.symm
    · exact G.loopless.irrefl _ hvw

end OneFlag

lemma raw_filter_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A : Finset (Fin n)} (v : Fin n) :
    (∀ x : Fin n → Bool, setOr A x = true → x v = true → graphFun G ∅ x = true) ↔
      ∀ a ∈ A, G.Adj a v := by
  constructor
  · intro h a ha
    apply (graphFun_pair_iff a v).mp
    exact h (pairInput a v) ((setOr_pair A a v).mpr (Or.inl ha)) (by simp [pairInput])
  · intro h x hx hv
    obtain ⟨a, ha, hxa⟩ := of_decide_eq_true hx
    exact (graphFun_iff x).mpr ⟨a, v, h a ha, hxa, hv⟩

lemma setOr_le_iff {n : ℕ} (A B : Finset (Fin n)) :
    (∀ x : Fin n → Bool, setOr A x = true → setOr B x = true) ↔ A ⊆ B := by
  constructor
  · intro h a ha
    have hv := h (fun v => decide (v = a)) (by
      simp only [setOr, decide_eq_true_eq]
      exact ⟨a, ha, by simp⟩)
    simp only [setOr, decide_eq_true_eq] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    exact hb
  · intro h x hx
    simp only [setOr, decide_eq_true_eq] at hx ⊢
    obtain ⟨a, ha, hxa⟩ := hx
    exact ⟨a, h ha, hxa⟩

lemma no_common_neighbor_not_le_setOr {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)}
    (hA : ¬ ∃ v : Fin n, ∀ a ∈ A, G.Adj a v)
    (hB : ∃ v : Fin n, ∀ b ∈ B, G.Adj b v) :
    ¬ ∀ x : Fin n → Bool, setOr A x = true → setOr B x = true := by
  intro h
  obtain ⟨v, hv⟩ := hB
  exact hA ⟨v, fun a ha => hv a ((setOr_le_iff A B).mp h ha)⟩

lemma raw_filter_bad_of_no_common_neighbor {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A : Finset (Fin n)}
    (hA : ¬ ∃ v : Fin n, ∀ a ∈ A, G.Adj a v) (v : Fin n) :
    ∃ x : Fin n → Bool, setOr A x = true ∧ x v = true ∧ graphFun G ∅ x = false := by
  have hex : ∃ a ∈ A, ¬ G.Adj a v := by
    by_contra h
    apply hA
    refine ⟨v, ?_⟩
    intro a ha
    by_contra hav
    exact h ⟨a, ha, hav⟩
  obtain ⟨a, ha, hav⟩ := hex
  refine ⟨pairInput a v, (setOr_pair A a v).mpr (Or.inl ha), by simp [pairInput], ?_⟩
  apply Bool.eq_false_iff.mpr
  intro hf
  exact hav ((graphFun_pair_iff a v).mp hf)

lemma nonempty_setOr_not_below_graphFun {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A : Finset (Fin n)} (hA : A.Nonempty) :
    ¬ ∀ x : Fin n → Bool, setOr A x = true → graphFun G ∅ x = true := by
  obtain ⟨a, ha⟩ := hA
  intro h
  have hF := h (pairInput a a) ((setOr_pair A a a).mpr (Or.inl ha))
  exact G.loopless.irrefl a ((graphFun_pair_iff a a).mp hF)


namespace MixedFactors

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma mixed_raw_filter_separates_colors {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {A C D : Finset (Fin n)}
    (hA : ∀ b : Bool, ∃ a ∈ A, s a = b)
    (hclean : ∀ x : Fin n → Bool,
      setOr A x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    ∀ c ∈ C, ∀ d ∈ D, s c ≠ s d := by
  intro c hc d hd hcd
  obtain ⟨a, ha, hsa⟩ := hA (s c)
  let x : Fin n → Bool := fun v => decide (s v = s c)
  have hxa : x a = true := by simp [x, hsa]
  have hxc : x c = true := by simp [x]
  have hxd : x d = true := by simp [x, hcd]
  have hF := hclean x
    (by simp only [setOr, decide_eq_true_eq]; exact ⟨a, ha, hxa⟩)
    (by simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq]
        exact ⟨⟨c, hc, hxc⟩, ⟨d, hd, hxd⟩⟩)
  obtain ⟨u, v, huv, hxu, hxv⟩ := (graphFun_iff x).mp hF
  simp only [x, decide_eq_true_eq] at hxu hxv
  exact hbip u v huv (hxu.trans hxv.symm)

lemma mixed_raw_filter_forces_pure_product {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {A C D : Finset (Fin n)}
    (hA : ∀ b : Bool, ∃ a ∈ A, s a = b)
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hclean : ∀ x : Fin n → Bool,
      setOr A x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    ∃ b : Bool, (∀ c ∈ C, s c = b) ∧ (∀ d ∈ D, s d = !b) := by
  have hsep := mixed_raw_filter_separates_colors s hbip hA hclean
  obtain ⟨c, hc⟩ := hC
  obtain ⟨d, hd⟩ := hD
  refine ⟨s c, ?_, ?_⟩
  · intro c' hc'
    have h1 := hsep c hc d hd
    have h2 := hsep c' hc' d hd
    cases hsc : s c <;> cases hsc' : s c' <;> cases hsd : s d <;> simp_all
  · intro d' hd'
    have h1 := hsep c hc d' hd'
    cases hsc : s c <;> cases hsd' : s d' <;> simp_all

end MixedFactors


namespace ClauseColors

open PEqualNP.MetaComplexity.NestedCover

lemma clean_clauses_has_pure_factor {n k : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (clause : Fin k → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, setOr (clause i) x = true) → graphFun G ∅ x = true) (b : Bool) :
    ∃ i, ∀ v ∈ clause i, s v = !b := by
  have hex : ∃ i, ¬ ∃ v ∈ clause i, s v = b := by
    by_contra h
    push Not at h
    let x : Fin n → Bool := fun v => decide (s v = b)
    have hF := hclean x (by
      intro i
      obtain ⟨v, hv, hsv⟩ := h i
      simp only [setOr, decide_eq_true_eq]
      exact ⟨v, hv, by simp [x, hsv]⟩)
    obtain ⟨u, v, huv, hxu, hxv⟩ := (graphFun_iff x).mp hF
    simp only [x, decide_eq_true_eq] at hxu hxv
    exact hbip u v huv (hxu.trans hxv.symm)
  obtain ⟨i, hi⟩ := hex
  refine ⟨i, ?_⟩
  intro v hv
  have hne : s v ≠ b := fun h => hi ⟨v, hv, h⟩
  cases hsv : s v <;> cases hb : b <;> simp_all

lemma clean_four_clauses_two_mixed_bound {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    (clause : Fin 4 → Finset (Fin n)) (hne : ∀ i, (clause i).Nonempty)
    (hclean : ∀ x : Fin n → Bool,
      (∀ i, setOr (clause i) x = true) → graphFun G ∅ x = true) :
    (Finset.univ.filter fun i : Fin 4 => ∀ b : Bool, ∃ v ∈ clause i, s v = b).card ≤ 2 := by
  obtain ⟨i, hi⟩ := clean_clauses_has_pure_factor s hbip clause hclean false
  obtain ⟨j, hj⟩ := clean_clauses_has_pure_factor s hbip clause hclean true
  have hij : i ≠ j := by
    intro e
    obtain ⟨v, hv⟩ := hne i
    have h1 := hi v hv
    have h2 := hj v (e ▸ hv)
    simp only [Bool.not_false, Bool.not_true] at h1 h2
    rw [h1] at h2
    contradiction
  have hsub : (Finset.univ.filter fun a : Fin 4 => ∀ b : Bool, ∃ v ∈ clause a, s v = b) ⊆
      Finset.univ \ {i, j} := by
    intro a ha
    have ham := (Finset.mem_filter.mp ha).2
    have hai : a ≠ i := by
      rintro rfl
      obtain ⟨v, hv, hsv⟩ := ham false
      have h1 := hi v hv
      simp only [Bool.not_false] at h1
      rw [hsv] at h1
      contradiction
    have haj : a ≠ j := by
      rintro rfl
      obtain ⟨v, hv, hsv⟩ := ham true
      have h1 := hj v hv
      simp only [Bool.not_true] at h1
      rw [hsv] at h1
      contradiction
    simp [hai, haj]
  have hc := Finset.card_le_card hsub
  have hp : ({i, j} : Finset (Fin 4)).card = 2 := Finset.card_pair hij
  have he : (Finset.univ \ ({i, j} : Finset (Fin 4))).card = 2 := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hp]
  omega

end ClauseColors


namespace Frontier

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

lemma sole_reader_of_frontier {n : ℕ} {C : Circuit}
    (hAO : IsAO2 n C) {p g : ℕ} {P : ℕ → Prop}
    (hp : p < C.gates.length) (hg : g < C.gates.length)
    (hpg : n + p ∈ (gateAt C g).inputs) (hPp : P p)
    (hlive : ∀ i < C.gates.length,
      C.output = n + i ∨ ∃ j < C.gates.length, n + i ∈ (gateAt C j).inputs)
    (houtput : ∀ i < C.gates.length, P i → C.output ≠ n + i)
    (hor : ∀ i < C.gates.length, P i → ∀ j < C.gates.length,
      (gateAt C j).op = GateOp.or → n + i ∈ (gateAt C j).inputs → P j)
    (hand : ∀ i < C.gates.length, P i → ∀ j < C.gates.length,
      (gateAt C j).op = GateOp.and → n + i ∈ (gateAt C j).inputs → j = g)
    (hoperand : ∀ i < C.gates.length, P i → n + i ∈ (gateAt C g).inputs → i = p) :
    readers n C p = {g} := by
  have noLater : ∀ d i, C.gates.length - i = d → i < C.gates.length → p < i → P i → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro i hdi hi hpi hPi
      rcases hlive i hi with hout | ⟨j, hj, hread⟩
      · exact houtput i hi hPi hout
      · have hij := read_index_lt hAO hj hread
        rcases gate_op_cases hAO hj with handj | horj
        · have hjg := hand i hi hPi j hj handj hread
          subst j
          have := hoperand i hi hPi hread
          omega
        · exact ih (C.gates.length - j) (by omega) j rfl hj (by omega)
            (hor i hi hPi j hj horj hread)
  apply Finset.ext
  intro j
  simp only [readers, Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hread⟩
    have hpj := read_index_lt hAO hj hread
    rcases gate_op_cases hAO hj with handj | horj
    · exact hand p hp hPp j hj handj hread
    · exact False.elim (noLater _ j rfl hj hpj (hor p hp hPp j hj horj hread))
  · rintro rfl
    exact ⟨hg, hpg⟩


lemma not_orReach_of_clean_raw_filter {n : ℕ} {G : SimpleGraph (Fin n)}
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

lemma sole_reader_of_dirty_filters {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : PEqualNP.MetaComplexity.circuitFun n C = graphFun G ∅)
    {g h p : ℕ} (c : Fin 2) (hp : p < C.gates.length) (hgN : g < C.gates.length)
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hroot : opnd C g c = n + p)
    (hlive : ∀ i < C.gates.length,
      C.output = n + i ∨ ∃ j < C.gates.length, n + i ∈ (gateAt C j).inputs)
    (hraw : ∀ u : Fin n, ∃ x,
      gateVal n C p x = true ∧ x u = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hgfilter : ∃ v : Fin n, ∀ x,
      W n C x (opnd C g (1 - c)) = true → x v = true → graphFun G ∅ x = true)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n C x (opnd C h b) = true → x v = true → graphFun G ∅ x = true) :
    readers n C p = {g} := by
  have hpg : n + p ∈ (gateAt C g).inputs := by
    rw [← hroot, gate_inputs_eq hAO hgN]
    fin_cases c <;> simp
  have hnoother : ¬ OrReaches n C (opnd C g (1 - c)) p :=
    not_orReach_of_clean_raw_filter hraw hgfilter
  have hnoh : ∀ b : Fin 2, ¬ OrReaches n C (opnd C h b) p := fun b =>
    not_orReach_of_clean_raw_filter hraw (hhfilter b)
  apply sole_reader_of_frontier hAO (P := fun i => OrReaches n C (n + i) p)
    hp hgN hpg (orReach_self n C p hp) hlive
  · intro i _ hPi hout
    obtain ⟨x, hpx, _, hneg⟩ := hg
    have hv := reach_up n C x (n + i) p hPi hpx
    rw [← hout] at hv
    change PEqualNP.MetaComplexity.circuitFun n C x = true at hv
    rw [hcompute, hneg] at hv
    exact Bool.false_ne_true hv
  · intro i _ hPi j hj hop hread
    exact orReach_trans n C j hj hop (n + i) hread (hAO.2.1 j hj _ hread) p hPi
  · intro i _ hPi j hj hop hread
    rcases and_reader_is_junk_of_witnesses hAO hTF hJ hj hop hread hPi hraw hg hh with hjg | hjh
    · exact hjg
    · subst j
      have hmem : n + i = opnd C h 0 ∨ n + i = opnd C h 1 := by
        simpa only [gate_inputs_eq hAO hj, List.mem_cons, List.not_mem_nil, or_false] using hread
      rcases hmem with heq | heq
      · exact False.elim (hnoh 0 (by rw [← heq]; exact hPi))
      · exact False.elim (hnoh 1 (by rw [← heq]; exact hPi))
  · intro i _ hPi hread
    have hmem0 : n + i = opnd C g 0 ∨ n + i = opnd C g 1 := by
      simpa only [gate_inputs_eq hAO hgN, List.mem_cons, List.not_mem_nil, or_false] using hread
    have hmem : n + i = opnd C g c ∨ n + i = opnd C g (1 - c) := by
      fin_cases c
      · simpa using hmem0
      · simpa using hmem0.symm
    rcases hmem with heq | heq
    · rw [hroot] at heq
      omega
    · exact False.elim (hnoother (by rw [← heq]; exact hPi))

end Frontier

end PEqualNP.Outside.L_meta_5012
