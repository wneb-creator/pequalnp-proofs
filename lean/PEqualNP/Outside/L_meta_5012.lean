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


namespace PreserveEdges

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma universal_neighbor_unique {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {B : Finset (Fin n)}
    (hB : 2 ≤ B.card) {u z : Fin n}
    (hu : ∀ b ∈ B, G.Adj u b) (hz : ∀ b ∈ B, G.Adj z b) : u = z := by
  apply Finset.card_le_one.mp (universalTo_card_le_one h4 hB)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩

lemma mutual_common_subset_centers {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A B C D : Finset (Fin n)}
    (hB : 2 ≤ B.card) (hD : 2 ≤ D.card) {u z : Fin n}
    (huB : ∀ b ∈ B, G.Adj u b) (hzD : ∀ d ∈ D, G.Adj z d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true) :
    A ∩ C ⊆ {u,z} := by
  intro a ha
  rcases mutual_common_vertex_filter hBD hclean ha with h | h
  · have he := universal_neighbor_unique h4 hB h huB
    simp [he]
  · have he := universal_neighbor_unique h4 hD h hzD
    simp [he]

lemma filtered_rectangle_center {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {A B : Finset (Fin n)}
    (hA : ¬ ∃ v : Fin n, ∀ a ∈ A, G.Adj a v)
    (hB : 2 ≤ B.card) {u a b w : Fin n}
    (huB : ∀ v ∈ B, G.Adj u v) (ha : a ∈ A) (hb : b ∈ B)
    (hw : w = a ∨ w = b)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → x w = true → graphFun G ∅ x = true) : a = u := by
  rcases hw with hwa | hwb
  · subst w
    apply universal_neighbor_unique h4 hB ?_ huB
    intro d hd
    apply (graphFun_pair_iff a d).mp
    apply hclean (pairInput a d)
    · simp only [setProduct, Bool.and_eq_true, setOr_pair]
      exact ⟨Or.inl ha, Or.inr hd⟩
    · simp [pairInput]
  · subst w
    exfalso
    apply hA
    refine ⟨b, ?_⟩
    intro d hd
    apply (graphFun_pair_iff d b).mp
    apply hclean (pairInput d b)
    · simp only [setProduct, Bool.and_eq_true, setOr_pair]
      exact ⟨Or.inl hd, Or.inr hb⟩
    · simp [pairInput]

lemma two_center_preserves_mutual_pairs {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (h4 : NoFourCycle G) {A B C D : Finset (Fin n)}
    (hB : 2 ≤ B.card) (hD : 2 ≤ D.card) {u z : Fin n}
    (huB : ∀ b ∈ B, G.Adj u b) (hzD : ∀ d ∈ D, G.Adj z d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hAs : ∀ a ∈ A, s a = false) (hBs : ∀ b ∈ B, s b = true)
    (hCs : ∀ c ∈ C, s c = false) (hDs : ∀ d ∈ D, s d = true)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true)
    (a b : Fin n)
    (hg : setProduct A B (pairInput a b) = true)
    (hh : setProduct C D (pairInput a b) = true) :
    setProduct {u,z} B (pairInput a b) = true := by
  have hs := mutual_common_subset_centers h4 hB hD huB hzD hBD hclean
  rcases (mutual_pair_trace s hAs hBs hCs hDs a b).mp ⟨hg, hh⟩ with h | h
  · simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inl (hs h.1), Or.inr (Finset.mem_inter.mp h.2).1⟩
  · simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inr (hs h.1), Or.inl (Finset.mem_inter.mp h.2).1⟩

lemma two_center_preserves_filtered_pairs {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool) (h4 : NoFourCycle G)
    {A B : Finset (Fin n)}
    (hA : ¬ ∃ v : Fin n, ∀ a ∈ A, G.Adj a v)
    (hB : 2 ≤ B.card) {u z : Fin n} (huB : ∀ b ∈ B, G.Adj u b)
    (hAs : ∀ a ∈ A, s a = false) (hBs : ∀ b ∈ B, s b = true)
    {w : Fin n}
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → x w = true → graphFun G ∅ x = true)
    (a b : Fin n) (hg : setProduct A B (pairInput a b) = true)
    (hw : pairInput a b w = true) :
    setProduct {u,z} B (pairInput a b) = true := by
  have hw' : w = a ∨ w = b := of_decide_eq_true hw
  have ht := (mutual_pair_trace s hAs hBs hAs hBs a b).mp ⟨hg,hg⟩
  simp only [Finset.mem_inter, and_self] at ht
  rcases ht with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · have he := filtered_rectangle_center h4 hA hB huB ha hb hw' hclean
    simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inl (by simp [he]), Or.inr hb⟩
  · have he := filtered_rectangle_center h4 hA hB huB hb ha hw'.symm hclean
    simp only [setProduct, Bool.and_eq_true, setOr_pair]
    exact ⟨Or.inr (by simp [he]), Or.inl ha⟩

end PreserveEdges


namespace NonflagPair

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def CrossStar {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) : Prop :=
  ∃ u ∈ A, ∃ v ∈ B, (∀ a ∈ A, G.Adj a v) ∧ ∀ b ∈ B, G.Adj u b

lemma clean_at_left {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A B : Finset (Fin n)} {u : Fin n} (hu : ∀ b ∈ B, G.Adj u b) :
    ∀ x : Fin n → Bool, setProduct A B x = true → x u = true → graphFun G ∅ x = true := by
  intro x hx hxu
  simp only [setProduct, Bool.and_eq_true] at hx
  have hb := hx.2
  obtain ⟨b, hb, hxb⟩ := of_decide_eq_true hb
  exact (graphFun_iff x).mpr ⟨u,b,hu b hb,hxu,hxb⟩

lemma clean_at_right {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {A B : Finset (Fin n)} {u : Fin n} (hu : ∀ a ∈ A, G.Adj a u) :
    ∀ x : Fin n → Bool, setProduct A B x = true → x u = true → graphFun G ∅ x = true := by
  intro x hx hxu
  simp only [setProduct, Bool.and_eq_true] at hx
  have ha := hx.1
  obtain ⟨a, ha, hxa⟩ := of_decide_eq_true ha
  exact (graphFun_iff x).mpr ⟨a,u,hu a ha,hxa,hxu⟩

lemma mutual_rect_safe_endpoint_of_other_nonflag {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A B C D : Finset (Fin n)}
    (hAC : ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true)
    (hnoflag : ¬ CrossStar G C D) {u v : Fin n}
    (hu : u ∈ A ∩ C) (hv : v ∈ B ∩ D) :
    (∀ x : Fin n → Bool, setProduct A B x = true → x u = true → graphFun G ∅ x = true) ∨
    (∀ x : Fin n → Bool, setProduct A B x = true → x v = true → graphFun G ∅ x = true) := by
  rcases mutual_common_vertex_filter hBD hclean hu with huB | huD
  · exact Or.inl (clean_at_left huB)
  have hswap : ∀ x : Fin n → Bool,
      setProduct B A x = true → setProduct D C x = true → graphFun G ∅ x = true := by
    intro x hx hy
    exact hclean x (by simpa only [setProduct_comm B A] using hx)
      (by simpa only [setProduct_comm D C] using hy)
  rcases mutual_common_vertex_filter hAC hswap hv with hvA | hvC
  · exact Or.inr (clean_at_right (fun a ha => (hvA a ha).symm))
  · exfalso
    exact hnoflag ⟨u, (Finset.mem_inter.mp hu).2, v, (Finset.mem_inter.mp hv).2,
      (fun c hc => (hvC c hc).symm), huD⟩

lemma mutual_pair_safe_endpoint_of_other_nonflag {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v)
    {A B C D : Finset (Fin n)}
    (hAs : ∀ a ∈ A, s a = false) (hBs : ∀ b ∈ B, s b = true)
    (hCs : ∀ c ∈ C, s c = false) (hDs : ∀ d ∈ D, s d = true)
    (hclean : ∀ x : Fin n → Bool,
      setProduct A B x = true → setProduct C D x = true → graphFun G ∅ x = true)
    (hnoflag : ¬ CrossStar G C D) (u v : Fin n)
    (hg : setProduct A B (pairInput u v) = true)
    (hh : setProduct C D (pairInput u v) = true) :
    (∀ x : Fin n → Bool, setProduct A B x = true → x u = true → graphFun G ∅ x = true) ∨
    (∀ x : Fin n → Bool, setProduct A B x = true → x v = true → graphFun G ∅ x = true) := by
  have hAC : ∀ a ∈ A, ∀ c ∈ C, ¬ G.Adj a c := by
    intro a ha c hc
    exact bipartite_same_color_nonadj s hbip ((hAs a ha).trans (hCs c hc).symm)
  have hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d := by
    intro b hb d hd
    exact bipartite_same_color_nonadj s hbip ((hBs b hb).trans (hDs d hd).symm)
  rcases (mutual_pair_trace s hAs hBs hCs hDs u v).mp ⟨hg,hh⟩ with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact mutual_rect_safe_endpoint_of_other_nonflag hAC hBD hclean hnoflag hu hv
  · exact (mutual_rect_safe_endpoint_of_other_nonflag hAC hBD hclean hnoflag hv hu).symm

end NonflagPair


namespace OneFlagIsolation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma one_flag_root_sole_reader {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hAO : IsAO2 n K) (hTF : TopForm G K)
    (hcompute : circuitFun n K = graphFun G ∅)
    {g h p : ℕ} (c : Fin 2) (hp : p < K.gates.length) (hgN : g < K.gates.length)
    (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hroot : opnd K g c = n + p)
    (hlive : ∀ i < K.gates.length,
      K.output = n + i ∨ ∃ j < K.gates.length, n + i ∈ (gateAt K j).inputs)
    {A B C D : Finset (Fin n)} {u z t a : Fin n}
    (hAp : ∀ x, gateVal n K p x = setOr A x)
    (hABg : ∀ x, gateVal n K g x = setProduct A B x)
    (hCDh : ∀ x, gateVal n K h x = setProduct C D x)
    (hBoperand : ∀ x, Frontier.W n K x (opnd K g (1 - c)) = setOr B x)
    (hCoperand : ∀ x, Frontier.W n K x (opnd K h 0) = setOr C x)
    (hDoperand : ∀ x, Frontier.W n K x (opnd K h 1) = setOr D x)
    (hu : u ∈ A) (hzA : z ∈ A) (ha : a ∈ A) (huz : u ≠ z)
    (htB : t ∈ B) (hzC : z ∈ C)
    (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (huB : ∀ b ∈ B, G.Adj u b)
    (hCt : ∀ v ∈ C, G.Adj v t) (hzD : ∀ d ∈ D, G.Adj z d)
    (hat : ¬ G.Adj a t) : readers n K p = {g} := by
  have hut := huB t htB
  have hzt := hCt z hzC
  have hA := OneFlag.no_common_neighbor_of_bad_member h4 hu hzA ha huz hut hzt hat
  apply Frontier.sole_reader_of_dirty_filters hAO hTF hcompute c hp hgN hJ hroot hlive
  · intro v
    obtain ⟨x, hAx, hxv, hneg⟩ := raw_filter_bad_of_no_common_neighbor hA v
    exact ⟨x, by rw [hAp]; exact hAx, hxv, hneg⟩
  · refine ⟨pairInput a t, ?_, ?_, ?_⟩
    · rw [hAp]
      exact (setOr_pair A a t).mpr (Or.inl ha)
    · rw [hABg]
      simp only [setProduct, Bool.and_eq_true, setOr_pair]
      exact ⟨Or.inl ha, Or.inr htB⟩
    · apply Bool.eq_false_iff.mpr
      intro hf
      exact hat ((graphFun_pair_iff a t).mp hf)
  · obtain ⟨x, hAx, hCDx, hneg⟩ :=
      OneFlag.one_flag_raw_side_bad_witness s hbip h4 hu huz hut hzt hC hD hCt hzD
    exact ⟨x, by rw [hAp]; exact hAx, by rw [hCDh]; exact hCDx, hneg⟩
  · refine ⟨u, ?_⟩
    intro x hBx hxu
    apply (raw_filter_iff u).mpr (fun b hb => (huB b hb).symm) x _ hxu
    rw [← hBoperand]
    exact hBx
  · intro b
    fin_cases b
    · refine ⟨t, ?_⟩
      intro x hCx hxt
      apply (raw_filter_iff t).mpr hCt x _ hxt
      rw [← hCoperand]
      exact hCx
    · refine ⟨z, ?_⟩
      intro x hDx hxz
      apply (raw_filter_iff z).mpr (fun d hd => (hzD d hd).symm) x _ hxz
      rw [← hDoperand]
      exact hDx

end OneFlagIsolation


namespace EdgePreservation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Frontier

lemma raise_orReach_U {n : ℕ} {K : Circuit} {U : ℕ → Bool}
    (hor : ∀ j < K.gates.length, (gateAt K j).op = GateOp.or →
      ∀ w ∈ (gateAt K j).inputs, U w = true → U (n + j) = true)
    {w p : ℕ} (hr : OrReaches n K w p) (hp : U (n + p) = true) : U w = true := by
  have go : ∀ k, k < K.gates.length → p ∈ (orSets n K).getD k [] → U (n + k) = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk hmem
      rcases (orSets_mem_iff n K k p hk).mp hmem with heq | ⟨hop, v, hv, hn, hlt, hsub⟩
      · rw [← heq]
        exact hp
      · have hvU := ih (v - n) (by omega) (by omega) hsub
        have heq : n + (v - n) = v := by omega
        rw [heq] at hvU
        exact hor k hk hop v hv hvU
  obtain ⟨hn, hmem⟩ := hr
  have hw : w - n < K.gates.length := by
    by_contra h
    have hlen : (orSets n K).length = K.gates.length := by
      unfold orSets
      rw [orFold_length]
      simp
    have hge : (orSets n K).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem
  have hv := go (w - n) hw hmem
  have heq : n + (w - n) = w := by omega
  rw [heq] at hv
  exact hv

lemma raise_orIn_U {n : ℕ} {K : Circuit} {U : ℕ → Bool}
    (hor : ∀ j < K.gates.length, (gateAt K j).op = GateOp.or →
      ∀ w ∈ (gateAt K j).inputs, U w = true → U (n + j) = true)
    {w : ℕ} {u : Fin n} (hu : u ∈ orIn n K w) (hUu : U u.val = true) : U w = true := by
  rcases (orIn_mem n K w u).mp hu with heq | ⟨j, hj, hr, hop, hinput⟩
  · rw [← heq]
    exact hUu
  · exact raise_orReach_U hor hr (hor j hj hop u.val hinput hUu)

lemma operand_frontier {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    {g h j w : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hj : j < K.gates.length) (hop : (gateAt K j).op = GateOp.and)
    (hw : w ∈ (gateAt K j).inputs) (x : Fin n → Bool) (hval : W n K x w = true) :
    (∃ u : Fin n, u ∈ orIn n K w ∧ x u = true) ∨
      (OrReaches n K w g ∧ gateVal n K g x = true) ∨
      (OrReaches n K w h ∧ gateVal n K h x = true) := by
  rcases down n K x (fun k hk => hAO.1 _ (gateAt_mem' K k hk)) w hval with
    hraw | ⟨k, hk, hr, hopk, hkv⟩
  · exact Or.inl hraw
  · have hnotbelow : ¬ BelowF G K k := by
      intro hclean
      exact hTF k hk j hj hopk hclean hop
        (reach_cone n K j hj w hw (hAO.2.1 j hj w hw) k hr)
    have hkJ : k ∈ junk G K := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr hk, hopk, hk, ?_⟩
      unfold BelowF at hnotbelow
      push Not at hnotbelow
      obtain ⟨y, hy, hf⟩ := hnotbelow
      exact ⟨y, hy, by simpa using hf⟩
    rcases hJ k hkJ with rfl | rfl
    · exact Or.inr (Or.inl ⟨hr, hkv⟩)
    · exact Or.inr (Or.inr ⟨hr, hkv⟩)

lemma and_pair_true {n : ℕ} {K : Circuit} (hAO : IsAO2 n K)
    {j a b : ℕ} (hj : j < K.gates.length) (hop : (gateAt K j).op = GateOp.and)
    (hinputs : (gateAt K j).inputs = [a,b] ∨ (gateAt K j).inputs = [b,a])
    (x : Fin n → Bool) (ha : W n K x a = true) (hb : W n K x b = true) :
    gateVal n K j x = true := by
  apply W_and n K x j hj hop
  intro w hw
  refine ⟨hAO.2.1 j hj w hw, ?_⟩
  rcases hinputs with hlist | hlist
  · simp only [hlist, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ha
    · exact hb
  · simp only [hlist, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hb
    · exact ha

lemma gate_binary_eval {n : ℕ} {K : Circuit} (hAO : IsAO2 n K)
    {j : ℕ} (hj : j < K.gates.length) (x : Fin n → Bool) :
    gateVal n K j x = (gateAt K j).op.eval
      [W n K x (opnd K j 0), W n K x (opnd K j 1)] := by
  change W n K x (n + j) = _
  rw [W_gate n K x j hj, gate_inputs_eq hAO hj]
  have h0 : opnd K j 0 < n + j := hAO.2.1 j hj _ (by rw [gate_inputs_eq hAO hj]; simp)
  have h1 : opnd K j 1 < n + j := hAO.2.1 j hj _ (by rw [gate_inputs_eq hAO hj]; simp)
  simp [h0, h1]

lemma clean_context_retains_g {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    {g h j a b : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgdirty : ∃ y, gateVal n K g y = true ∧ graphFun G ∅ y = false)
    (hj : j < K.gates.length) (hop : (gateAt K j).op = GateOp.and)
    (hclean : BelowF G K j)
    (hinputs : (gateAt K j).inputs = [a,b] ∨ (gateAt K j).inputs = [b,a])
    (x : Fin n → Bool) (R : Bool)
    (hraw : ∀ v : Fin n,
      (∀ y, gateVal n K g y = true → y v = true → graphFun G ∅ y = true) →
      gateVal n K g x = true → x v = true → R = true)
    (hmutual : (∀ y, gateVal n K g y = true → gateVal n K h y = true →
        graphFun G ∅ y = true) → gateVal n K g x = true → gateVal n K h x = true → R = true)
    (hag : OrReaches n K a g) (hgx : gateVal n K g x = true)
    (hbx : W n K x b = true) : R = true := by
  have hb : b ∈ (gateAt K j).inputs := by
    rcases hinputs with hlist | hlist <;> simp [hlist]
  rcases operand_frontier hAO hTF hJ hj hop hb x hbx with
    ⟨v, hv, hxv⟩ | ⟨hbg, hgv⟩ | ⟨hbh, hhv⟩
  · apply hraw v _ hgx hxv
    intro y hgy hyv
    exact hclean y (and_pair_true hAO hj hop hinputs y
      (reach_up n K y a g hag hgy) (orIn_val hv y hyv))
  · obtain ⟨y, hgy, hneg⟩ := hgdirty
    have hf := hclean y (and_pair_true hAO hj hop hinputs y
      (reach_up n K y a g hag hgy) (reach_up n K y b g hbg hgy))
    rw [hneg] at hf
    exact False.elim (Bool.false_ne_true hf)
  · apply hmutual _ hgx hhv
    intro y hgy hhy
    exact hclean y (and_pair_true hAO hj hop hinputs y
      (reach_up n K y a g hag hgy) (reach_up n K y b h hbh hhy))

lemma clean_and_positive_preserved {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    {g h j : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgdirty : ∃ y, gateVal n K g y = true ∧ graphFun G ∅ y = false)
    (hj : j < K.gates.length) (hop : (gateAt K j).op = GateOp.and)
    (hclean : BelowF G K j) (x : Fin n → Bool) (U : ℕ → Bool)
    (hinput : ∀ v : Fin n, x v = true → U v.val = true)
    (hor : ∀ k < K.gates.length, (gateAt K k).op = GateOp.or →
      ∀ w ∈ (gateAt K k).inputs, U w = true → U (n + k) = true)
    (hand : U (n + j) = (U (opnd K j 0) && U (opnd K j 1)))
    (hhkeep : gateVal n K h x = true → U (n + h) = true)
    (hraw : ∀ v : Fin n,
      (∀ y, gateVal n K g y = true → y v = true → graphFun G ∅ y = true) →
      gateVal n K g x = true → x v = true → U (n + g) = true)
    (hmutual : (∀ y, gateVal n K g y = true → gateVal n K h y = true →
        graphFun G ∅ y = true) → gateVal n K g x = true → gateVal n K h x = true → U (n + g) = true)
    (hjx : gateVal n K j x = true) : U (n + j) = true := by
  have keepSide : ∀ a b,
      ((gateAt K j).inputs = [a,b] ∨ (gateAt K j).inputs = [b,a]) →
      W n K x a = true → W n K x b = true → U a = true := by
    intro a b hinputs hax hbx
    have ha : a ∈ (gateAt K j).inputs := by
      rcases hinputs with hlist | hlist <;> simp [hlist]
    rcases operand_frontier hAO hTF hJ hj hop ha x hax with
      ⟨v, hv, hxv⟩ | ⟨hag, hgx⟩ | ⟨hah, hhx⟩
    · exact raise_orIn_U hor hv (hinput v hxv)
    · have hgU := clean_context_retains_g hAO hTF hJ hgdirty hj hop hclean
        hinputs x (U (n + g)) hraw hmutual hag hgx hbx
      exact raise_orReach_U hor hag hgU
    · exact raise_orReach_U hor hah (hhkeep hhx)
  have hvals : W n K x (opnd K j 0) = true ∧ W n K x (opnd K j 1) = true := by
    rw [gate_binary_eval hAO hj x, hop] at hjx
    simpa only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
      Bool.and_eq_true] using hjx
  rw [hand, Bool.and_eq_true]
  exact ⟨keepSide _ _ (Or.inl (gate_inputs_eq hAO hj)) hvals.1 hvals.2,
    keepSide _ _ (Or.inr (gate_inputs_eq hAO hj)) hvals.2 hvals.1⟩

lemma clean_gate_positive_preserved {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    {g h : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgdirty : ∃ y, gateVal n K g y = true ∧ graphFun G ∅ y = false)
    (x : Fin n → Bool) (U : ℕ → Bool)
    (hinput : ∀ v : Fin n, x v = true → U v.val = true)
    (hor : ∀ k < K.gates.length, (gateAt K k).op = GateOp.or →
      ∀ w ∈ (gateAt K k).inputs, U w = true → U (n + k) = true)
    (hand : ∀ k < K.gates.length, (gateAt K k).op = GateOp.and → BelowF G K k →
      U (n + k) = (U (opnd K k 0) && U (opnd K k 1)))
    (hhkeep : gateVal n K h x = true → U (n + h) = true)
    (hraw : ∀ v : Fin n,
      (∀ y, gateVal n K g y = true → y v = true → graphFun G ∅ y = true) →
      gateVal n K g x = true → x v = true → U (n + g) = true)
    (hmutual : (∀ y, gateVal n K g y = true → gateVal n K h y = true →
        graphFun G ∅ y = true) → gateVal n K g x = true → gateVal n K h x = true → U (n + g) = true) :
    ∀ j < K.gates.length, BelowF G K j → gateVal n K j x = true → U (n + j) = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hclean hjx
    rcases hAO.1 _ (gateAt_mem' K j hj) with hop | hop
    · exact clean_and_positive_preserved hAO hTF hJ hgdirty hj hop hclean x U
        hinput hor (hand j hj hop hclean) hhkeep hraw hmutual hjx
    · change W n K x (n + j) = true at hjx
      rw [W_gate n K x j hj, hop] at hjx
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hjx
      obtain ⟨w, hw, hwx⟩ := hjx
      have hback := hAO.2.1 j hj w hw
      rw [ite_eq_left hback] at hwx
      apply hor j hj hop w hw
      by_cases hwn : w < n
      · apply hinput ⟨w, hwn⟩
        rw [W_input n K x w hwn] at hwx
        exact hwx
      · have heq : n + (w - n) = w := by omega
        have hk : w - n < K.gates.length := by omega
        have hkclean : BelowF G K (w - n) := by
          intro y hky
          have hwy : W n K y w = true := by
            rw [← heq]
            exact hky
          exact hclean y (W_or n K y j hj hop w hw hback hwy)
        have hkv : gateVal n K (w - n) x = true := by
          change W n K x (n + (w - n)) = true
          rw [heq]
          exact hwx
        have hu := ih (w - n) (by omega) hk hkclean hkv
        rw [heq] at hu
        exact hu

lemma output_positive_preserved {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    (hcompute : circuitFun n K = graphFun G ∅)
    {g h : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgdirty : ∃ y, gateVal n K g y = true ∧ graphFun G ∅ y = false)
    (x : Fin n → Bool) (U : ℕ → Bool)
    (hinput : ∀ v : Fin n, x v = true → U v.val = true)
    (hor : ∀ k < K.gates.length, (gateAt K k).op = GateOp.or →
      ∀ w ∈ (gateAt K k).inputs, U w = true → U (n + k) = true)
    (hand : ∀ k < K.gates.length, (gateAt K k).op = GateOp.and → BelowF G K k →
      U (n + k) = (U (opnd K k 0) && U (opnd K k 1)))
    (hhkeep : gateVal n K h x = true → U (n + h) = true)
    (hraw : ∀ v : Fin n,
      (∀ y, gateVal n K g y = true → y v = true → graphFun G ∅ y = true) →
      gateVal n K g x = true → x v = true → U (n + g) = true)
    (hmutual : (∀ y, gateVal n K g y = true → gateVal n K h y = true →
        graphFun G ∅ y = true) → gateVal n K g x = true → gateVal n K h x = true → U (n + g) = true)
    (hFx : graphFun G ∅ x = true) : U K.output = true := by
  have hval : W n K x K.output = true := by
    change circuitFun n K x = true
    rw [hcompute]
    exact hFx
  have hbound : K.output < n + K.gates.length := by
    by_contra hge
    have hlen := wires_length n K x
    have hfalse : W n K x K.output = false := getD_ge_length _ K.output (by omega)
    rw [hfalse] at hval
    exact Bool.false_ne_true hval
  by_cases hout : K.output < n
  · apply hinput ⟨K.output, hout⟩
    rw [W_input n K x K.output hout] at hval
    exact hval
  · have heq : n + (K.output - n) = K.output := by omega
    have hj : K.output - n < K.gates.length := by omega
    have hclean : BelowF G K (K.output - n) := by
      intro y hy
      have houty : circuitFun n K y = true := by
        change W n K y K.output = true
        rw [← heq]
        exact hy
      rw [hcompute] at houty
      exact houty
    have hgate : gateVal n K (K.output - n) x = true := by
      change W n K x (n + (K.output - n)) = true
      rw [heq]
      exact hval
    have hu := clean_gate_positive_preserved hAO hTF hJ hgdirty x U
      hinput hor hand hhkeep hraw hmutual _ hj hclean hgate
    rw [heq] at hu
    exact hu

lemma output_positive_preserved_of_gate_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    (hcompute : circuitFun n K = graphFun G ∅)
    {g h : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgop : (gateAt K g).op = GateOp.and)
    (hgdirty : ∃ y, gateVal n K g y = true ∧ graphFun G ∅ y = false)
    (x : Fin n → Bool) (U : ℕ → Bool)
    (hinput : ∀ v : Fin n, U v.val = x v)
    (hgate : ∀ k < K.gates.length, k ≠ g →
      U (n + k) = (gateAt K k).op.eval ((gateAt K k).inputs.map U))
    (hhkeep : gateVal n K h x = true → U (n + h) = true)
    (hraw : ∀ v : Fin n,
      (∀ y, gateVal n K g y = true → y v = true → graphFun G ∅ y = true) →
      gateVal n K g x = true → x v = true → U (n + g) = true)
    (hmutual : (∀ y, gateVal n K g y = true → gateVal n K h y = true →
        graphFun G ∅ y = true) → gateVal n K g x = true → gateVal n K h x = true → U (n + g) = true)
    (hFx : graphFun G ∅ x = true) : U K.output = true := by
  apply output_positive_preserved hAO hTF hcompute hJ hgdirty x U
  · intro v hv
    rw [hinput]
    exact hv
  · intro k hk hop w hw hUw
    have hkg : k ≠ g := by
      intro heq
      rw [heq, hgop] at hop
      contradiction
    rw [hgate k hk hkg, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨w, hw, hUw⟩
  · intro k hk hop hclean
    have hkg : k ≠ g := by
      rintro rfl
      obtain ⟨y, hgy, hneg⟩ := hgdirty
      have hf := hclean y hgy
      rw [hneg] at hf
      exact Bool.false_ne_true hf
    rw [hgate k hk hkg, hop, gate_inputs_eq hAO hk]
    simp [GateOp.eval]
  · exact hhkeep
  · exact hraw
  · exact hmutual
  · exact hFx

lemma output_eq_graph_of_gate_eq {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    (hcompute : circuitFun n K = graphFun G ∅)
    {g h : ℕ} (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgop : (gateAt K g).op = GateOp.and)
    (hgdirty : ∃ y, gateVal n K g y = true ∧ graphFun G ∅ y = false)
    (U : (Fin n → Bool) → ℕ → Bool)
    (hinput : ∀ x (v : Fin n), U x v.val = x v)
    (hgate : ∀ x k, k < K.gates.length → k ≠ g →
      U x (n + k) = (gateAt K k).op.eval ((gateAt K k).inputs.map (U x)))
    (hhkeep : ∀ x, gateVal n K h x = true → U x (n + h) = true)
    (hraw : ∀ u v : Fin n, G.Adj u v → ∀ w : Fin n,
      (∀ y, gateVal n K g y = true → y w = true → graphFun G ∅ y = true) →
      gateVal n K g (pairInput u v) = true → pairInput u v w = true →
      U (pairInput u v) (n + g) = true)
    (hmutual : ∀ u v : Fin n, G.Adj u v →
      (∀ y, gateVal n K g y = true → gateVal n K h y = true → graphFun G ∅ y = true) →
      gateVal n K g (pairInput u v) = true → gateVal n K h (pairInput u v) = true →
      U (pairInput u v) (n + g) = true)
    (hmono : ∀ x y : Fin n → Bool, (∀ v, x v = true → y v = true) →
      U x K.output = true → U y K.output = true)
    (hunder : ∀ x, U x K.output = true → graphFun G ∅ x = true) :
    ∀ x, U x K.output = graphFun G ∅ x := by
  intro x
  rw [Bool.eq_iff_iff]
  constructor
  · exact hunder x
  · intro hFx
    obtain ⟨u, v, huv, hxu, hxv⟩ := (graphFun_iff x).mp hFx
    have hpair : U (pairInput u v) K.output = true :=
      output_positive_preserved_of_gate_eq hAO hTF hcompute hJ hgop hgdirty
        (pairInput u v) (U (pairInput u v)) (hinput _) (hgate _) (hhkeep _)
        (hraw u v huv) (hmutual u v huv) ((graphFun_pair_iff u v).mpr huv)
    apply hmono (pairInput u v) x _ hpair
    intro w hw
    simp only [pairInput, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl
    · exact hxu
    · exact hxv

end EdgePreservation


namespace RootPatch

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Frontier

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

lemma patch_length (C : Circuit) (j : ℕ) (g : Gate) :
    (patch C j g).gates.length = C.gates.length := by
  simp [patch]

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma gateAt_patch_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) :
    gateAt (patch C j g) j = g := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, hj]

lemma patch_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (j : ℕ) (g : Gate)
    (hOp : g.op = GateOp.and ∨ g.op = GateOp.or) (hLen : g.inputs.length = 2)
    (hBack : ∀ w ∈ g.inputs, w < n + j) : IsAO2 n (patch C j g) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.1 k hk
    · exact hOp
  · intro k hk w hw
    have hkC : k < C.gates.length := by simpa only [patch_length] using hk
    by_cases hkj : k = j
    · subst k
      rw [gateAt_patch_eq hkC] at hw
      exact hBack w hw
    · rw [gateAt_patch_ne C j k g (Ne.symm hkj)] at hw
      exact hAO.2.1 k hkC w hw
  · intro k hk
    change k ∈ C.gates.set j g at hk
    rcases List.mem_or_eq_of_mem_set hk with hk | rfl
    · exact hAO.2.2 k hk
    · exact hLen

lemma patch_size (C : Circuit) (p : ℕ) (r : Gate) : (patch C p r).size = C.size := by
  simp [Circuit.size, patch_length]

lemma W_gate_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map (W n C x)) := by
  rw [W_gate n C x k hk]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hAO.2.1 k hk w hw)]

lemma patch_W_eq_before {n : ℕ} {C : Circuit} {p : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r)) (x : Fin n → Bool)
    (w : ℕ) (hwp : w < n + p) (hwN : w < n + C.gates.length) :
    W n (patch C p r) x w = W n C x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [W_input n (patch C p r) x w hw, W_input n C x w hw]
    · have hn : n ≤ w := by omega
      have hk : w - n < C.gates.length := by omega
      have hk' : w - n < (patch C p r).gates.length := by simpa [patch_length] using hk
      have hne : p ≠ w - n := by omega
      have he : n + (w - n) = w := by omega
      conv_lhs => rw [← he]
      conv_rhs => rw [← he]
      rw [W_gate_eq hAO' x hk', W_gate_eq hAO x hk,
        gateAt_patch_ne C p (w - n) r hne]
      congr 1
      apply List.map_congr_left
      intro v hv
      have hvw := hAO.2.1 (w - n) hk v hv
      exact ih v (by omega) (by omega) (by omega)

def restored (n : ℕ) (C : Circuit) (p : ℕ) (r : Gate)
    (x : Fin n → Bool) (w : ℕ) : Bool :=
  if w = n + p then W n C x w else W n (patch C p r) x w

lemma restored_input {n : ℕ} (C : Circuit) (p : ℕ) (r : Gate)
    (x : Fin n → Bool) (v : Fin n) : restored n C p r x v.val = x v := by
  rw [restored, ite_eq_right (by omega), W_input n (patch C p r) x v.val v.isLt]

lemma restored_eq_patch {n : ℕ} (C : Circuit) (p : ℕ) (r : Gate)
    (x : Fin n → Bool) {w : ℕ} (hw : w ≠ n + p) :
    restored n C p r x w = W n (patch C p r) x w := by
  exact ite_eq_right hw

lemma restored_gate_eq {n : ℕ} {C : Circuit} {p g : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (hread : ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g)
    (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) (hkg : k ≠ g) :
    restored n C p r x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map (restored n C p r x)) := by
  by_cases hkp : k = p
  · subst k
    rw [restored, ite_eq_left rfl, W_gate_eq hAO x hk]
    congr 1
    apply List.map_congr_left
    intro v hv
    have hvp := hAO.2.1 p hk v hv
    rw [restored, ite_eq_right (by omega)]
    exact (patch_W_eq_before hAO hAO' x v hvp (by omega)).symm
  · have hk' : k < (patch C p r).gates.length := by simpa [patch_length] using hk
    rw [restored_eq_patch C p r x (by omega), W_gate_eq hAO' x hk',
      gateAt_patch_ne C p k r (Ne.symm hkp)]
    congr 1
    apply List.map_congr_left
    intro v hv
    have hvp : v ≠ n + p := by
      intro e
      subst v
      exact hkg (hread k hk hv)
    exact (restored_eq_patch C p r x hvp).symm

lemma sole_reader_property {n : ℕ} {C : Circuit} {p g : ℕ}
    (hread : readers n C p = {g}) :
    ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g := by
  intro k hk hw
  have hm : k ∈ readers n C p := by simp [readers, hk, hw]
  rw [hread, Finset.mem_singleton] at hm
  exact hm


lemma patch_W_eq_before_reader {n : ℕ} {C : Circuit} {p g : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (hread : ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g)
    (x : Fin n → Bool) (w : ℕ) (hwg : w < n + g)
    (hwN : w < n + C.gates.length) (hwp : w ≠ n + p) :
    W n (patch C p r) x w = W n C x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w < n
    · rw [W_input n (patch C p r) x w hw, W_input n C x w hw]
    · have hn : n ≤ w := by omega
      have hk : w - n < C.gates.length := by omega
      have hk' : w - n < (patch C p r).gates.length := by simpa [patch_length] using hk
      have hne : p ≠ w - n := by omega
      have he : n + (w - n) = w := by omega
      conv_lhs => rw [← he]
      conv_rhs => rw [← he]
      rw [W_gate_eq hAO' x hk', W_gate_eq hAO x hk,
        gateAt_patch_ne C p (w - n) r hne]
      congr 1
      apply List.map_congr_left
      intro v hv
      have hvw := hAO.2.1 (w - n) hk v hv
      have hvp : v ≠ n + p := by
        intro e
        subst v
        have := hread (w - n) hk hv
        omega
      exact ih v (by omega) (by omega) (by omega) hvp

def rawOr {n : ℕ} (u z : Fin n) : Gate := ⟨GateOp.or, [u.val, z.val]⟩

lemma rawOr_patch_AO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (p : ℕ) (u z : Fin n) : IsAO2 n (patch C p (rawOr u z)) := by
  apply patch_isAO2 hAO p (rawOr u z)
  · exact Or.inr rfl
  · rfl
  · intro w hw
    simp only [rawOr, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl <;> omega

lemma rawOr_patch_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p : ℕ} (hp : p < C.gates.length) (u z : Fin n) (x : Fin n → Bool) :
    W n (patch C p (rawOr u z)) x (n + p) = (x u || x z) := by
  rw [W_gate_eq (rawOr_patch_AO2 hAO p u z) x (by simpa [patch_length] using hp),
    gateAt_patch_eq hp]
  simp only [rawOr, List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    Bool.or_false, id_eq]
  rw [W_input n _ x u.val u.isLt, W_input n _ x z.val z.isLt]

lemma rawOr_reader_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p g t : ℕ} (hp : p < C.gates.length) (hg : g < C.gates.length)
    (hread : ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g)
    (hop : (gateAt C g).op = GateOp.and)
    (hins : (gateAt C g).inputs = [n + p, t] ∨ (gateAt C g).inputs = [t, n + p])
    (ht : t ≠ n + p) (u z : Fin n) (x : Fin n → Bool) :
    restored n C p (rawOr u z) x (n + g) = ((x u || x z) && W n C x t) := by
  have hpm : n + p ∈ (gateAt C g).inputs := by rcases hins with h | h <;> simp [h]
  have htm : t ∈ (gateAt C g).inputs := by rcases hins with h | h <;> simp [h]
  have hpg := hAO.2.1 g hg (n + p) hpm
  have htg := hAO.2.1 g hg t htm
  have hAO' := rawOr_patch_AO2 hAO p u z
  have htv := patch_W_eq_before_reader hAO hAO' hread x t htg (by omega) ht
  rw [restored_eq_patch C p (rawOr u z) x (by omega),
    W_gate_eq hAO' x (by simpa [patch_length] using hg),
    gateAt_patch_ne C p g (rawOr u z) (by omega), hop]
  rcases hins with hins | hins
  · simp only [hins, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, Bool.and_true, id_eq]
    rw [rawOr_patch_value hAO hp, htv]
  · simp only [hins, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, Bool.and_true, id_eq]
    rw [rawOr_patch_value hAO hp, htv, Bool.and_comm]

lemma patch_W_eq_of_no_cone {n : ℕ} {C : Circuit} {p : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hkp : k ≠ p) (hnc : ¬ InCone n C p k) :
    W n (patch C p r) x (n + k) = W n C x (n + k) := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [W_gate_eq hAO' x (by simpa [patch_length] using hk), W_gate_eq hAO x hk,
      gateAt_patch_ne C p k r (Ne.symm hkp)]
    congr 1
    apply List.map_congr_left
    intro w hw
    by_cases hwn : w < n
    · rw [W_input n _ x w hwn, W_input n _ x w hwn]
    · have hlow : n ≤ w := by omega
      have hhigh := hAO.2.1 k hk w hw
      have he : n + (w - n) = w := by omega
      have hne : w - n ≠ p := by
        intro e
        exact hnc ((inCone_iff n C p k).mpr
          ⟨hk, w - n, by omega, by simpa [he] using hw, Or.inl e.symm⟩)
      have hnc' : ¬ InCone n C p (w - n) := by
        intro h
        exact hnc ((inCone_iff n C p k).mpr
          ⟨hk, w - n, by omega, by simpa [he] using hw, Or.inr h⟩)
      have hv := ih (w - n) (by omega) (by omega) hne hnc'
      simpa [he] using hv

lemma restored_gate_of_no_cone {n : ℕ} {C : Circuit} {p k : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (x : Fin n → Bool) (hk : k < C.gates.length) (hkp : k ≠ p)
    (hnc : ¬ InCone n C p k) :
    restored n C p r x (n + k) = W n C x (n + k) := by
  rw [restored_eq_patch C p r x (by omega)]
  exact patch_W_eq_of_no_cone hAO hAO' x k hk hkp hnc


lemma eval_true_mono (gate : Gate) (hop : gate.op = GateOp.and ∨ gate.op = GateOp.or)
    (f h : ℕ → Bool) (hfh : ∀ w ∈ gate.inputs, f w = true → h w = true)
    (hf : gate.op.eval (gate.inputs.map f) = true) :
    gate.op.eval (gate.inputs.map h) = true := by
  rcases hop with hop | hop
  · simp only [hop, GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hf ⊢
    intro w hw
    exact hfh w hw (hf w hw)
  · simp only [hop, GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hf ⊢
    obtain ⟨w, hw, hfw⟩ := hf
    exact ⟨w, hw, hfh w hw hfw⟩

lemma W_large (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) : W n C x w = false := by
  exact getD_ge_length _ w (by rw [wires_length]; exact hw)

lemma W_true_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ)
    (hx : W n C x w = true) : W n C y w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [W_input n C x w hwn] at hx
      rw [W_input n C y w hwn]
      exact hxy ⟨w, hwn⟩ hx
    · by_cases hwN : w < n + C.gates.length
      · have hk : w - n < C.gates.length := by omega
        have he : n + (w - n) = w := by omega
        have hx' : W n C x (n + (w - n)) = true := by simpa [he] using hx
        rw [W_gate_eq hAO x hk] at hx'
        have hy := eval_true_mono (gateAt C (w - n))
          (hAO.1 _ (gateAt_mem' C _ hk)) (W n C x) (W n C y) (by
            intro v hv hvx
            exact ih v (by have := hAO.2.1 (w - n) hk v hv; omega) hvx) hx'
        rw [← W_gate_eq hAO y hk, he] at hy
        exact hy
      · rw [W_large n C x w (by omega)] at hx
        contradiction

lemma restored_true_mono {n : ℕ} {C : Circuit} {p : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) (w : ℕ)
    (hx : restored n C p r x w = true) : restored n C p r y w = true := by
  unfold restored at hx ⊢
  split_ifs at hx ⊢ with h
  · exact W_true_mono hAO x y hxy w hx
  · exact W_true_mono hAO' x y hxy w hx

lemma patch_under {n : ℕ} {C : Circuit} {p : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (x : Fin n → Bool)
    (hroot : W n (patch C p r) x (n + p) = true → W n C x (n + p) = true)
    (w : ℕ) (hx : W n (patch C p r) x w = true) : W n C x w = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [W_input n (patch C p r) x w hwn] at hx
      rw [W_input n C x w hwn]
      exact hx
    · by_cases hwN : w < n + C.gates.length
      · by_cases hwp : w = n + p
        · subst w
          exact hroot hx
        · have hk : w - n < C.gates.length := by omega
          have hk' : w - n < (patch C p r).gates.length := by simpa [patch_length] using hk
          have he : n + (w - n) = w := by omega
          have hx' : W n (patch C p r) x (n + (w - n)) = true := by simpa [he] using hx
          rw [W_gate_eq hAO' x hk', gateAt_patch_ne C p (w - n) r (by omega)] at hx'
          have hy := eval_true_mono (gateAt C (w - n))
            (hAO.1 _ (gateAt_mem' C _ hk)) (W n (patch C p r) x) (W n C x) (by
              intro v hv hvx
              exact ih v (by have := hAO.2.1 (w - n) hk v hv; omega) hvx) hx'
          rw [← W_gate_eq hAO x hk, he] at hy
          exact hy
      · rw [W_large n (patch C p r) x w (by rw [patch_length]; omega)] at hx
        contradiction

lemma rawOr_patch_under {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p : ℕ} (hp : p < C.gates.length) (u z : Fin n) (x : Fin n → Bool)
    (hu : x u = true → W n C x (n + p) = true)
    (hz : x z = true → W n C x (n + p) = true)
    (w : ℕ) (hx : W n (patch C p (rawOr u z)) x w = true) : W n C x w = true := by
  apply patch_under hAO (rawOr_patch_AO2 hAO p u z) x _ w hx
  intro hp'
  rw [rawOr_patch_value hAO hp, Bool.or_eq_true] at hp'
  exact hp'.elim hu hz

lemma restored_under {n : ℕ} {C : Circuit} {p : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (x : Fin n → Bool)
    (hroot : W n (patch C p r) x (n + p) = true → W n C x (n + p) = true)
    (w : ℕ) (hx : restored n C p r x w = true) : W n C x w = true := by
  unfold restored at hx
  split_ifs at hx with h
  · exact hx
  · exact patch_under hAO hAO' x hroot w hx

lemma restored_or_raise {n : ℕ} {C : Circuit} {p g : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (hread : ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g)
    (hgop : (gateAt C g).op = GateOp.and)
    (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length)
    (hkop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hv : restored n C p r x w = true) : restored n C p r x (n + k) = true := by
  have hkg : k ≠ g := by intro e; subst k; rw [hgop] at hkop; contradiction
  rw [restored_gate_eq hAO hAO' hread x hk hkg, hkop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨w, hw, hv⟩

lemma restored_and_eq {n : ℕ} {C : Circuit} {p g : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (hread : ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g)
    (x : Fin n → Bool) {k : ℕ} (hk : k < C.gates.length) (hkg : k ≠ g)
    (hop : (gateAt C k).op = GateOp.and) :
    restored n C p r x (n + k) =
      (restored n C p r x (opnd C k 0) && restored n C p r x (opnd C k 1)) := by
  rw [restored_gate_eq hAO hAO' hread x hk hkg, hop, gate_inputs_eq hAO hk]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
    List.all_nil, Bool.and_true, id_eq]


lemma sole_reader_cone {n : ℕ} {C : Circuit} {p g : ℕ}
    (hread : ∀ k, k < C.gates.length → n + p ∈ (gateAt C k).inputs → k = g)
    (k : ℕ) (hp : InCone n C p k) : k = g ∨ InCone n C g k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    obtain ⟨hk, j, hjk, hjin, hpj⟩ := (inCone_iff n C p k).mp hp
    rcases hpj with h | h
    · subst j
      exact Or.inl (hread k hk hjin)
    · rcases ih j hjk h with e | hgj
      · exact Or.inr ((inCone_iff n C g k).mpr ⟨hk, j, hjk, hjin, Or.inl e.symm⟩)
      · exact Or.inr ((inCone_iff n C g k).mpr ⟨hk, j, hjk, hjin, Or.inr hgj⟩)

lemma restored_independent_reader {n : ℕ} {C : Circuit} {p g k : ℕ} {r : Gate}
    (hAO : IsAO2 n C) (hAO' : IsAO2 n (patch C p r))
    (hread : ∀ j, j < C.gates.length → n + p ∈ (gateAt C j).inputs → j = g)
    (x : Fin n → Bool) (hk : k < C.gates.length) (hkp : k ≠ p)
    (hkg : k ≠ g) (hnc : ¬ InCone n C g k) :
    restored n C p r x (n + k) = W n C x (n + k) := by
  apply restored_gate_of_no_cone hAO hAO' x hk hkp
  intro h
  exact (sole_reader_cone hread k h).elim hkg hnc

end RootPatch

end PEqualNP.Outside.L_meta_5012
