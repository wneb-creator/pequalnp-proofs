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

namespace SmallFactorScratch

open PEqualNP.MetaComplexity.NestedCover

lemma crossStar_small_product_below {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A B : Finset (Fin n)}
    (hflag : NonflagPair.CrossStar G A B) (hsmall : A.card ≤ 1 ∨ B.card ≤ 1) :
    ∀ x : Fin n → Bool, setProduct A B x = true → graphFun G ∅ x = true := by
  obtain ⟨u,hu,v,hv,hAv,huB⟩ := hflag
  intro x hx
  simp only [setProduct, Bool.and_eq_true, setOr, decide_eq_true_eq] at hx
  obtain ⟨⟨a,ha,hxa⟩,b,hb,hxb⟩ := hx
  rcases hsmall with hA | hB
  · have hau : a = u := Finset.card_le_one.mp hA a ha u hu
    exact (graphFun_iff x).mpr ⟨a,b,hau ▸ huB b hb,hxa,hxb⟩
  · have hbv : b = v := Finset.card_le_one.mp hB b hb v hv
    exact (graphFun_iff x).mpr ⟨a,b,hbv ▸ hAv a ha,hxa,hxb⟩

lemma dirty_small_product_not_crossStar {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {A B : Finset (Fin n)}
    (hsmall : A.card ≤ 1 ∨ B.card ≤ 1)
    (hdirty : ∃ x : Fin n → Bool, setProduct A B x = true ∧ graphFun G ∅ x = false) :
    ¬ NonflagPair.CrossStar G A B := by
  intro hflag
  obtain ⟨x,hx,hneg⟩ := hdirty
  have hf := crossStar_small_product_below hflag hsmall x hx
  rw [hneg] at hf
  exact Bool.false_ne_true hf

end SmallFactorScratch

namespace OrientedIsolation

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma one_flag_root_sole_reader {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hAO : IsAO2 n K) (hTF : TopForm G K)
    (hcompute : circuitFun n K = graphFun G ∅)
    {g h p : ℕ} (c d : Fin 2) (hp : p < K.gates.length) (hgN : g < K.gates.length)
    (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hroot : opnd K g c = n + p)
    (hlive : ∀ i < K.gates.length,
      K.output = n + i ∨ ∃ j < K.gates.length, n + i ∈ (gateAt K j).inputs)
    {A B C D : Finset (Fin n)} {u z t a : Fin n}
    (hAp : ∀ x, gateVal n K p x = setOr A x)
    (hABg : ∀ x, gateVal n K g x = setProduct A B x)
    (hCDh : ∀ x, gateVal n K h x = setProduct C D x)
    (hBoperand : ∀ x, Frontier.W n K x (opnd K g (1 - c)) = setOr B x)
    (hCoperand : ∀ x, Frontier.W n K x (opnd K h d) = setOr C x)
    (hDoperand : ∀ x, Frontier.W n K x (opnd K h (1 - d)) = setOr D x)
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
    by_cases hb : b = d
    · subst b
      refine ⟨t, ?_⟩
      intro x hCx hxt
      apply (raw_filter_iff t).mpr hCt x _ hxt
      rw [← hCoperand]
      exact hCx
    · have he : b = 1 - d := by fin_cases b <;> fin_cases d <;> simp_all
      rw [he]
      refine ⟨z, ?_⟩
      intro x hDx hxz
      apply (raw_filter_iff z).mpr (fun d hd => (hzD d hd).symm) x _ hxz
      rw [← hDoperand]
      exact hDx

end OrientedIsolation

namespace HardOneFlagMeta

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier RootPatch

lemma patch_cone_subset_of_raw {n : ℕ} {C : Circuit} {p : ℕ} {r : Gate}
    (hraw : ∀ w ∈ r.inputs, w < n) {i j : ℕ} :
    InCone n (patch C p r) i j → InCone n C i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hc
    obtain ⟨hj', k, hkj, hkin, hik⟩ := (inCone_iff n (patch C p r) i j).mp hc
    have hj : j < C.gates.length := by simpa [patch_length] using hj'
    by_cases hjp : j = p
    · subst j
      rw [gateAt_patch_eq hj] at hkin
      have := hraw (n + k) hkin
      omega
    · rw [gateAt_patch_ne C p j r (Ne.symm hjp)] at hkin
      apply (inCone_iff n C i j).mpr
      refine ⟨hj, k, hkj, hkin, ?_⟩
      rcases hik with e | h
      · exact Or.inl e
      · exact Or.inr (ih k hkj h)

lemma rawOr_patch_cone_subset {n : ℕ} (C : Circuit) (p : ℕ) (u z : Fin n) {i j : ℕ}
    (h : InCone n (patch C p (rawOr u z)) i j) : InCone n C i j := by
  apply patch_cone_subset_of_raw _ h
  intro w hw
  simp only [rawOr, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> omega

lemma rawOr_ops_eq {n : ℕ} {C : Circuit} {p : ℕ} (u z : Fin n)
    (hpOR : (gateAt C p).op = GateOp.or) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt (patch C p (rawOr u z)) k).op = (gateAt C k).op := by
  by_cases hkp : k = p
  · subst k
    rw [gateAt_patch_eq hk]
    exact hpOR.symm
  · rw [gateAt_patch_ne C p k (rawOr u z) (Ne.symm hkp)]

lemma junk_subset_of_under {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hlen : D.gates.length = C.gates.length)
    (hop : ∀ k, k < C.gates.length → (gateAt D k).op = (gateAt C k).op)
    (hunder : ∀ (x : Fin n → Bool) w, W n D x w = true → W n C x w = true) :
    junk G D ⊆ junk G C := by
  intro k hk
  obtain ⟨hkr, hka, hkD, x, hx, hFx⟩ := Finset.mem_filter.mp hk
  have hkC : k < C.gates.length := by omega
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkC, ?_, hkC, x, ?_, hFx⟩
  · rw [← hop k hkC]
    exact hka
  · exact hunder x (n + k) hx

lemma junk_eq_of_two_dirty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} {g h : ℕ}
    (hsub : junk G D ⊆ junk G C)
    (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (hgnew : IsDirtyAnd n G D g) (hhnew : IsDirtyAnd n G D h) :
    junk G D = junk G C := by
  apply Finset.Subset.antisymm hsub
  intro k hk
  rcases (hjunk k).mp hk with rfl | rfl
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hgnew.2.1, hgnew⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hhnew.2.1, hhnew⟩

lemma topForm_of_cone_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hlen : D.gates.length = C.gates.length)
    (hop : ∀ i, i < C.gates.length → (gateAt D i).op = (gateAt C i).op)
    (hcone : ∀ i j, InCone n D i j → InCone n C i j)
    (hjunk : junk G C ⊆ junk G D) (hT : TopForm G C) : TopForm G D := by
  intro i hi j hj hiand hib hjand hc
  have hiC : i < C.gates.length := by omega
  have hjC : j < C.gates.length := by omega
  have hiop : (gateAt C i).op = GateOp.and := (hop i hiC).symm.trans hiand
  have hjop : (gateAt C j).op = GateOp.and := (hop j hjC).symm.trans hjand
  have hibC : BelowF G C i := by
    intro x hx
    by_contra hf
    have hm : i ∈ junk G C := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiC, hiop, hiC, x, hx,
        Bool.eq_false_iff.mpr hf⟩
    obtain ⟨_, _, _, y, hy, hyF⟩ := Finset.mem_filter.mp (hjunk hm)
    have := hib y hy
    rw [hyF] at this
    cases this
  exact hT i hiC j hjC hiop hibC hjop (hcone i j hc)

lemma rawOr_isLeastAO {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (p : ℕ) (u z : Fin n)
    (hF : circuitFun n (patch C p (rawOr u z)) = graphFun G ∅) :
    IsLeastAO G (patch C p (rawOr u z)) := by
  refine ⟨rawOr_patch_AO2 hL.1 p u z, hF, ?_⟩
  intro D hD hDF
  rw [patch_size]
  exact hL.2.2 D hD hDF

lemma rawOr_preserves_structure {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {p g h : ℕ} (u z : Fin n)
    (hL : IsLeastAO G C) (hT : TopForm G C)
    (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (hpOR : (gateAt C p).op = GateOp.or)
    (hF : circuitFun n (patch C p (rawOr u z)) = graphFun G ∅)
    (hunder : ∀ (x : Fin n → Bool) w,
      W n (patch C p (rawOr u z)) x w = true → W n C x w = true)
    (hgnew : IsDirtyAnd n G (patch C p (rawOr u z)) g)
    (hhnew : IsDirtyAnd n G (patch C p (rawOr u z)) h) :
    IsLeastAO G (patch C p (rawOr u z)) ∧
      TopForm G (patch C p (rawOr u z)) ∧
      junk G (patch C p (rawOr u z)) = junk G C := by
  have hlen := patch_length C p (rawOr u z)
  have hop := rawOr_ops_eq u z hpOR
  have hsub := junk_subset_of_under (G := G) hlen hop hunder
  have heq := junk_eq_of_two_dirty hsub hjunk hgnew hhnew
  refine ⟨rawOr_isLeastAO hL p u z hF, ?_, heq⟩
  apply topForm_of_cone_subset hlen hop
    (fun i j hc => rawOr_patch_cone_subset C p u z hc) _ hT
  rw [heq]

end HardOneFlagMeta

namespace HardOneFlag

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm
open Frontier

lemma setOr_pair_vertices {n : ℕ} (u z : Fin n) (x : Fin n → Bool) :
    setOr {u,z} x = (x u || x z) := by
  rw [Bool.eq_iff_iff]
  simp [setOr]

lemma hard_one_flag_transform_core {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G K) (hTF : TopForm G K)
    {g h p : ℕ} (c d : Fin 2) (hgh : g ≠ h)
    (hJ : ∀ k, k ∈ junk G K ↔ k = g ∨ k = h)
    (hgnoth : ¬ InCone n K g h) (hhnog : ¬ InCone n K h g)
    (hroot : opnd K g c = n + p)
    (hlive : ∀ i < K.gates.length,
      K.output = n + i ∨ ∃ j < K.gates.length, n + i ∈ (gateAt K j).inputs)
    {A B C D : Finset (Fin n)} {u z t a : Fin n}
    (hAp : ∀ x, gateVal n K p x = setOr A x)
    (hABg : ∀ x, gateVal n K g x = setProduct A B x)
    (hCDh : ∀ x, gateVal n K h x = setProduct C D x)
    (hBoperand : ∀ x, W n K x (opnd K g (1 - c)) = setOr B x)
    (hCoperand : ∀ x, W n K x (opnd K h d) = setOr C x)
    (hDoperand : ∀ x, W n K x (opnd K h (1 - d)) = setOr D x)
    (hu : u ∈ A) (hzA : z ∈ A) (ha : a ∈ A) (huz : u ≠ z)
    (htB : t ∈ B) (hzC : z ∈ C)
    (hB : 2 ≤ B.card) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (huB : ∀ b ∈ B, G.Adj u b)
    (hCt : ∀ v ∈ C, G.Adj v t) (hzD : ∀ d ∈ D, G.Adj z d)
    (hat : ¬ G.Adj a t)
    (hAs : ∀ v ∈ A, s v = false) (hBs : ∀ v ∈ B, s v = true)
    (hCs : ∀ v ∈ C, s v = false) (hDs : ∀ v ∈ D, s v = true) :
    let K' := RootPatch.patch K p (RootPatch.rawOr u z)
    IsAO2 n K' ∧ circuitFun n K' = graphFun G ∅ ∧
    (∀ x, gateVal n K' g x = setProduct {u,z} B x) ∧
    (∀ x, gateVal n K' h x = setProduct C D x) ∧
    (∀ x w, W n K' x w = true → W n K x w = true) ∧
    (gateAt K p).op = GateOp.or := by
  dsimp only
  have hgJ := (hJ g).mpr (Or.inl rfl)
  have hhJ := (hJ h).mpr (Or.inr rfl)
  obtain ⟨hgR, hgop, hgN, hgdirty⟩ := Finset.mem_filter.mp hgJ
  obtain ⟨hhR, hhop, hhN, hhdirty⟩ := Finset.mem_filter.mp hhJ
  have hAO := hL.1
  have hrootmem : n + p ∈ (gateAt K g).inputs := by
    rw [← hroot, gate_inputs_eq hAO hgN]
    fin_cases c <;> simp
  have hpg : p < g := by
    have := hAO.2.1 g hgN (n + p) hrootmem
    omega
  have hpN : p < K.gates.length := by omega
  have hpneh : p ≠ h := by
    intro heq
    apply hhnog
    apply (inCone_iff n K h g).mpr
    refine ⟨hgN, p, hpg, hrootmem, ?_⟩
    exact Or.inl heq.symm
  have hut := huB t htB
  have hzt := hCt z hzC
  have hA := OneFlag.no_common_neighbor_of_bad_member h4 hu hzA ha huz hut hzt hat
  have hrootdirty : ∃ x, gateVal n K p x = true ∧ graphFun G ∅ x = false := by
    refine ⟨pairInput u u, ?_, ?_⟩
    · rw [hAp]
      exact (setOr_pair A u u).mpr (Or.inl hu)
    · apply Bool.eq_false_iff.mpr
      intro hf
      exact G.loopless.irrefl u ((graphFun_pair_iff u u).mp hf)
  have hpOR : (gateAt K p).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem' K p hpN) with hpAND | hpOR
    · have hpJ : p ∈ junk G K :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpN, hpAND, hpN, hrootdirty⟩
      rcases (hJ p).mp hpJ with heq | heq
      · omega
      · exact False.elim (hpneh heq)
    · exact hpOR
  have houtne : K.output ≠ n + p := by
    intro hout
    obtain ⟨x, hpx, hneg⟩ := hrootdirty
    have hv : circuitFun n K x = true := by
      change W n K x K.output = true
      rw [hout]
      exact hpx
    rw [hL.2.1, hneg] at hv
    exact Bool.false_ne_true hv
  have hsole := OrientedIsolation.one_flag_root_sole_reader s hbip h4 hAO hTF hL.2.1
    c d hpN hgN (fun k hk => (hJ k).mp hk) hroot hlive hAp hABg hCDh
    hBoperand hCoperand hDoperand hu hzA ha huz htB hzC hC hD huB hCt hzD hat
  have hread := RootPatch.sole_reader_property hsole
  have hAO' := RootPatch.rawOr_patch_AO2 hAO p u z
  have hotherne : opnd K g (1 - c) ≠ n + p := by
    intro heq
    apply no_common_neighbor_not_le_setOr hA ⟨u, fun b hb => (huB b hb).symm⟩
    intro x hAx
    have hBx := hBoperand x
    rw [heq] at hBx
    have hpx : W n K x (n + p) = true := by
      change gateVal n K p x = true
      rw [hAp]
      exact hAx
    exact hBx ▸ hpx
  have hins : (gateAt K g).inputs = [n + p, opnd K g (1 - c)] ∨
      (gateAt K g).inputs = [opnd K g (1 - c), n + p] := by
    have hlist := gate_inputs_eq hAO hgN
    fin_cases c
    · left
      change (gateAt K g).inputs = [n + p, opnd K g 1]
      change opnd K g 0 = n + p at hroot
      rw [← hroot]
      exact hlist
    · right
      change (gateAt K g).inputs = [opnd K g 0, n + p]
      change opnd K g 1 = n + p at hroot
      rw [← hroot]
      exact hlist
  let U := RootPatch.restored n K p (RootPatch.rawOr u z)
  have hUg : ∀ x, U x (n + g) = setProduct {u,z} B x := by
    intro x
    have hv := RootPatch.rawOr_reader_value hAO hpN hgN hread hgop hins hotherne u z x
    change U x (n + g) = _ at hv
    rw [hBoperand, ← setOr_pair_vertices u z x] at hv
    exact hv
  have hUh : ∀ x, U x (n + h) = gateVal n K h x := by
    intro x
    exact RootPatch.restored_independent_reader hAO hAO' hread x hhN hpneh.symm hgh.symm hgnoth
  have hrootUnder : ∀ x,
      W n (RootPatch.patch K p (RootPatch.rawOr u z)) x (n + p) = true →
      W n K x (n + p) = true := by
    intro x hx
    rw [RootPatch.rawOr_patch_value hAO hpN, Bool.or_eq_true] at hx
    change gateVal n K p x = true
    rw [hAp]
    simp only [setOr, decide_eq_true_eq]
    rcases hx with hxu | hxz
    · exact ⟨u, hu, hxu⟩
    · exact ⟨z, hzA, hxz⟩
  have hUnder : ∀ x w,
      W n (RootPatch.patch K p (RootPatch.rawOr u z)) x w = true → W n K x w = true := by
    intro x w hx
    exact RootPatch.patch_under hAO hAO' x (hrootUnder x) w hx
  have hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d := by
    intro b hb d hd hadj
    exact hbip b d hadj ((hBs b hb).trans (hDs d hd).symm)
  have hUout : ∀ x, U x K.output = graphFun G ∅ x := by
    apply EdgePreservation.output_eq_graph_of_gate_eq hAO hTF hL.2.1
      (fun k hk => (hJ k).mp hk) hgop hgdirty U
    · intro x v
      exact RootPatch.restored_input K p (RootPatch.rawOr u z) x v
    · intro x k hk hkg
      exact RootPatch.restored_gate_eq hAO hAO' hread x hk hkg
    · intro x hhx
      rw [hUh]
      exact hhx
    · intro v w _ q hfilter hgx hxq
      rw [hUg]
      apply PreserveEdges.two_center_preserves_filtered_pairs s h4 hA hB huB hAs hBs
      · intro y hy hyq
        apply hfilter y
        · rw [hABg]
          exact hy
        · exact hyq
      · rw [← hABg]
        exact hgx
      · exact hxq
    · intro v w _ hclean hgx hhx
      rw [hUg]
      apply PreserveEdges.two_center_preserves_mutual_pairs s h4 hB hD huB hzD hBD hAs hBs hCs hDs
      · intro y hgy hhy
        apply hclean y
        · rw [hABg]
          exact hgy
        · rw [hCDh]
          exact hhy
      · rw [← hABg]
        exact hgx
      · rw [← hCDh]
        exact hhx
    · intro x y hxy hx
      exact RootPatch.restored_true_mono hAO hAO' x y hxy K.output hx
    · intro x hx
      have hv := RootPatch.restored_under hAO hAO' x (hrootUnder x) K.output hx
      change circuitFun n K x = true at hv
      rw [hL.2.1] at hv
      exact hv
  refine ⟨hAO', ?_, ?_, ?_, hUnder, hpOR⟩
  · funext x
    change W n (RootPatch.patch K p (RootPatch.rawOr u z)) x K.output = graphFun G ∅ x
    rw [← RootPatch.restored_eq_patch K p (RootPatch.rawOr u z) x houtne]
    exact hUout x
  · intro x
    have hv := hUg x
    dsimp only [U] at hv
    rw [RootPatch.restored_eq_patch K p (RootPatch.rawOr u z) x (by omega)] at hv
    exact hv
  · intro x
    have hv := hUh x
    dsimp only [U] at hv
    rw [RootPatch.restored_eq_patch K p (RootPatch.rawOr u z) x (by omega), hCDh] at hv
    exact hv

def CrossStar {n : ℕ} (G : SimpleGraph (Fin n)) (K : Circuit) (k : ℕ) : Prop :=
  ∃ (A B : Finset (Fin n)) (u v : Fin n),
    G.Adj u v ∧ u ∈ A ∧ v ∈ B ∧
    (∀ a ∈ A, G.Adj a v) ∧ (∀ b ∈ B, G.Adj b u) ∧
    2 ≤ A.card ∧ 2 ≤ B.card ∧
    ∀ x, gateVal n K k x = setProduct A B x

lemma hard_one_flag_transform {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {K : Circuit} (s : Fin n → Bool)
    (hbip : ∀ u v, G.Adj u v → s u ≠ s v) (h4 : NoFourCycle G)
    (hL : IsLeastAO G K) (hTF : TopForm G K)
    {g h p : ℕ} (c d : Fin 2) (hgh : g ≠ h)
    (hJ : ∀ k, k ∈ junk G K ↔ k = g ∨ k = h)
    (hgnoth : ¬ InCone n K g h) (hhnog : ¬ InCone n K h g)
    (hroot : opnd K g c = n + p)
    (hlive : ∀ i < K.gates.length,
      K.output = n + i ∨ ∃ j < K.gates.length, n + i ∈ (gateAt K j).inputs)
    {A B C D : Finset (Fin n)} {u z t a : Fin n}
    (hAp : ∀ x, gateVal n K p x = setOr A x)
    (hABg : ∀ x, gateVal n K g x = setProduct A B x)
    (hCDh : ∀ x, gateVal n K h x = setProduct C D x)
    (hBoperand : ∀ x, W n K x (opnd K g (1 - c)) = setOr B x)
    (hCoperand : ∀ x, W n K x (opnd K h d) = setOr C x)
    (hDoperand : ∀ x, W n K x (opnd K h (1 - d)) = setOr D x)
    (hu : u ∈ A) (hzA : z ∈ A) (ha : a ∈ A) (huz : u ≠ z)
    (htB : t ∈ B) (hzC : z ∈ C) (htD : t ∈ D)
    (hB : 2 ≤ B.card) (hC : 2 ≤ C.card) (hD : 2 ≤ D.card)
    (huB : ∀ b ∈ B, G.Adj u b)
    (hCt : ∀ v ∈ C, G.Adj v t) (hzD : ∀ d ∈ D, G.Adj z d)
    (hat : ¬ G.Adj a t)
    (hAs : ∀ v ∈ A, s v = false) (hBs : ∀ v ∈ B, s v = true)
    (hCs : ∀ v ∈ C, s v = false) (hDs : ∀ v ∈ D, s v = true) :
    let K' := RootPatch.patch K p (RootPatch.rawOr u z)
    IsLeastAO G K' ∧ TopForm G K' ∧ K'.size = K.size ∧
    (∀ k, k ∈ junk G K' ↔ k = g ∨ k = h) ∧ CrossStar G K' g ∧ CrossStar G K' h := by
  dsimp only
  obtain ⟨hAO', hF', hSemg, hSemh, hUnder, hpOR⟩ :=
    hard_one_flag_transform_core s hbip h4 hL hTF c d hgh hJ hgnoth hhnog hroot hlive
      hAp hABg hCDh hBoperand hCoperand hDoperand hu hzA ha huz htB hzC hB hC hD
      huB hCt hzD hat hAs hBs hCs hDs
  have hgJ := (hJ g).mpr (Or.inl rfl)
  have hhJ := (hJ h).mpr (Or.inr rfl)
  obtain ⟨hgR, hgop, hgN, hgdirty⟩ := Finset.mem_filter.mp hgJ
  obtain ⟨hhR, hhop, hhN, hhdirty⟩ := Finset.mem_filter.mp hhJ
  have hgnew : IsDirtyAnd n G (RootPatch.patch K p (RootPatch.rawOr u z)) g := by
    refine ⟨(HardOneFlagMeta.rawOr_ops_eq u z hpOR g hgN).trans hgop, ?_, ?_⟩
    · simpa only [RootPatch.patch_length] using hgN
    · obtain ⟨x, hprod, hneg⟩ :=
        OneFlag.two_center_restriction_dirty h4 huz (huB t htB) (hCt z hzC) hB huB
      exact ⟨x, by rw [hSemg]; exact hprod, hneg⟩
  have hhnew : IsDirtyAnd n G (RootPatch.patch K p (RootPatch.rawOr u z)) h := by
    refine ⟨(HardOneFlagMeta.rawOr_ops_eq u z hpOR h hhN).trans hhop, ?_, ?_⟩
    · simpa only [RootPatch.patch_length] using hhN
    · obtain ⟨x, hhx, hneg⟩ := hhdirty
      refine ⟨x, ?_, hneg⟩
      rw [hSemh, ← hCDh]
      exact hhx
  obtain ⟨hL', hTF', hJ'⟩ :=
    HardOneFlagMeta.rawOr_preserves_structure u z hL hTF hJ hpOR hF' hUnder hgnew hhnew
  refine ⟨hL', hTF', RootPatch.patch_size K p (RootPatch.rawOr u z), ?_, ?_, ?_⟩
  · intro k
    rw [hJ']
    exact hJ k
  · refine ⟨{u,z}, B, u, t, huB t htB, by simp, htB, ?_, ?_, ?_, hB, hSemg⟩
    · intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact huB t htB
      · exact hCt _ hzC
    · intro b hb
      exact (huB b hb).symm
    · simp [Finset.card_pair huz]
  · exact ⟨C, D, z, t, hCt z hzC, hzC, htD, hCt,
      fun d hd => (hzD d hd).symm, hC, hD, hSemh⟩

end HardOneFlag

namespace HardOneFlagLift

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

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma below_wire_contains_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (w : ℕ) (hw : w < n + C.gates.length)
    (hb : ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true) :
    ∃ r, r < C.gates.length ∧ (gateAt C r).op = GateOp.and ∧ BelowF G C r ∧
      (r = w - n ∨ InCone n C r (w - n)) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    have hn : n ≤ w := by
      by_contra h
      exact input_not_belowF (by omega : w < n) hb
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    have hj : j < C.gates.length := by omega
    have hjb : BelowF G C j := hb
    rcases hAO.1 _ (gateAt_mem hj) with hand | hor
    · exact ⟨j, hj, hand, hjb, Or.inl (by omega)⟩
    · have hwb : ∀ x : Fin n → Bool, wval C x (opnd C j 0) = true → graphFun G ∅ x = true := by
        intro x hx
        apply hjb x
        rw [gateVal_eq_wval, wval_gate_or hAO x hj hor, Bool.or_eq_true]
        exact Or.inl hx
      have hlt := opnd_lt hAO hj 0
      have hn0 : n ≤ opnd C j 0 := by
        by_contra h
        exact input_not_belowF (by omega : opnd C j 0 < n) hwb
      obtain ⟨r, hr, hro, hrb, hrc⟩ := ih (opnd C j 0) hlt (by omega) hwb
      refine ⟨r, hr, hro, hrb, Or.inr ?_⟩
      simp only [Nat.add_sub_cancel_left]
      exact (inCone_iff hj).mpr ⟨opnd C j 0, opnd_mem hAO hj 0, hn0, hlt, hrc⟩

lemma cone_propagates_through_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {i j : ℕ} (hcone : InCone n C i j)
    (hor : ∀ k, InCone n C i k → (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (hi : gateVal n C i x = true) : gateVal n C j x = true := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len hcone
    have hop := hor j hcone
    obtain ⟨w, hw, hnw, hwj, hsub⟩ := (inCone_iff hj).mp hcone
    have hwv : wval C x w = true := by
      rcases hsub with he | hsub
      · rw [he, gateVal_eq_wval, Nat.add_sub_of_le hnw] at hi
        exact hi
      · have hg := ih (w - n) (by omega) hsub
        rw [gateVal_eq_wval, Nat.add_sub_of_le hnw] at hg
        exact hg
    rw [gateVal_eq_wval, wval_gate_or hAO x hj hop, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hj] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hwv
    · exact Or.inr hwv

lemma topForm_isLiftFixedPoint {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hF : circuitFun n C = graphFun G ∅)
    (hT : TopForm G C) : IsLiftFixedPoint G C := by
  rintro ⟨h, hh, b, hLive, _, hNot, hImp⟩
  have hwlt := opnd_lt hAO hh b
  obtain ⟨r, hr, hro, hrb, hrc⟩ :=
    below_wire_contains_top hAO (opnd C h b) (by omega) hImp.1
  have hwn : n ≤ opnd C h b := by
    by_contra hlt
    exact input_not_belowF (by omega : opnd C h b < n) hImp.1
  have hrh : InCone n C r h :=
    (inCone_iff hh).mpr ⟨opnd C h b, opnd_mem hAO hh b, hwn, hwlt, hrc⟩
  have hor : ∀ k, InCone n C h k → (gateAt C k).op = GateOp.or := by
    intro k hk
    have hkl := inCone_lt_len hk
    rcases hAO.1 _ (gateAt_mem hkl) with hand | hkor
    · exact False.elim (hT r hr k hkl hro hrb hand (inCone_trans hrh hk))
    · exact hkor
  apply hNot
  intro x hx
  have hout : wval C x C.output = true := by
    rcases hLive.2 with hout | ⟨houtn, hcone⟩
    · rw [hout]
      exact hx
    · have hc := cone_propagates_through_or hAO hcone hor x hx
      rw [gateVal_eq_wval, Nat.add_sub_of_le houtn] at hc
      exact hc
  change circuitFun n C x = true at hout
  rwa [hF] at hout

end HardOneFlagLift

namespace NoAlias

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  Frontier.W n C x w

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := Frontier.gateAt_eq C k hk

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wireVal n C w x = x ⟨w, hw⟩ := Frontier.W_input n C x w hw

lemma wireVal_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    wireVal n C (n + k) x = (gateAt C k).op.eval
      ((gateAt C k).inputs.map fun w => wireVal n C w x) := by
  change Frontier.W n C x (n + k) = (gateAt C k).op.eval
      ((gateAt C k).inputs.map (Frontier.W n C x))
  rw [Frontier.W_gate n C x k hk]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hRB k hk w hw)]

def remap (n g r w : ℕ) : ℕ :=
  if w < n + g then w
  else if w = n + g then r
  else w - 1

def origWire (n g w : ℕ) : ℕ :=
  if w < n + g then w else w + 1

def mapGate (f : ℕ → ℕ) (gt : Gate) : Gate :=
  ⟨gt.op, gt.inputs.map f⟩

def delGate (n g r : ℕ) (C : Circuit) : Circuit :=
  ⟨(C.gates.eraseIdx g).map (mapGate (remap n g r)), remap n g r C.output⟩

lemma delGate_length (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length) :
    (delGate n g r C).gates.length = C.gates.length - 1 := by
  simp [delGate, List.length_eraseIdx_of_lt hg]

lemma delGate_gateAt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (delGate n g r C) k =
      mapGate (remap n g r) (gateAt C (if k < g then k else k + 1)) := by
  have hk' : k < (delGate n g r C).gates.length := by
    rw [delGate_length n g r C hg]; exact hk
  rw [gateAt_eq_getElem (delGate n g r C) k hk']
  have hk_e : k < (C.gates.eraseIdx g).length := by
    rw [List.length_eraseIdx_of_lt hg]; exact hk
  simp only [delGate, List.getElem_map]
  split_ifs with hkg
  · rw [List.getElem_eraseIdx_of_lt hk_e hkg, gateAt_eq_getElem C k (by omega)]
  · rw [List.getElem_eraseIdx_of_ge hk_e (by omega), gateAt_eq_getElem C (k + 1) (by omega)]

lemma delGate_isAO2 (n g r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hg : g < C.gates.length) (hr : r < n + g) :
    IsAO2 n (delGate n g r C) := by
  rcases hAO with ⟨hAOOnly, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    exact hAOOnly gt0 (List.mem_of_mem_eraseIdx hgt0)
  · intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap
      split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap
      split_ifs <;> omega
  · intro gt hgt
    simp only [delGate, List.mem_map] at hgt
    obtain ⟨gt0, hgt0, rfl⟩ := hgt
    simp only [mapGate, List.length_map]
    exact hLen2 gt0 (List.mem_of_mem_eraseIdx hgt0)

lemma delGate_output_lt (n g r : ℕ) (C : Circuit) (hg : g < C.gates.length)
    (hr : r < n + g) (hout : C.output < n + C.gates.length) :
    (delGate n g r C).output < n + (delGate n g r C).gates.length := by
  rw [delGate_length n g r C hg]
  simp only [delGate, remap]
  split_ifs <;> omega

lemma origWire_remap_ne (n g r u : ℕ) (hne : u ≠ n + g) :
    origWire n g (remap n g r u) = u := by
  unfold origWire remap
  split_ifs <;> omega

lemma origWire_remap_eq (n g r : ℕ) (hr : r < n + g) :
    origWire n g (remap n g r (n + g)) = r := by
  unfold origWire remap
  split_ifs <;> omega

lemma delGate_wireVal_eq (n g r : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hRB : ReadsBack n C) (hg : g < C.gates.length) (hr : r < n + g)
    (hmatch : wireVal n C (n + g) x = wireVal n C r x) :
    ∀ w < n + (delGate n g r C).gates.length,
      wireVal n (delGate n g r C) w x = wireVal n C (origWire n g w) x := by
  have hAO_rb : ReadsBack n (delGate n g r C) := by
    intro k hk w' hw'
    rw [delGate_length n g r C hg] at hk
    rw [delGate_gateAt n g r C hg k hk] at hw'
    simp only [mapGate, List.mem_map] at hw'
    obtain ⟨w, hw, rfl⟩ := hw'
    split_ifs at hw with hkg
    · have hlt := hRB k (by omega) w hw
      unfold remap; split_ifs <;> omega
    · have hlt := hRB (k + 1) (by omega) w hw
      unfold remap; split_ifs <;> omega
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wireVal_input n (delGate n g r C) x w hwn]
      have horig : origWire n g w = w := by unfold origWire; split_ifs <;> omega
      rw [horig, wireVal_input n C x w hwn]
    · set k := w - n with hk_def
      have hw_eq : w = n + k := by omega
      have hk_lt : k < (delGate n g r C).gates.length := by omega
      have hk_lt' : k < C.gates.length - 1 := by
        rw [← delGate_length n g r C hg]; exact hk_lt
      rw [hw_eq, wireVal_gate n (delGate n g r C) x k hk_lt hAO_rb]
      rw [delGate_gateAt n g r C hg k hk_lt']
      set k0 := if k < g then k else k + 1 with hk0_def
      have hk0_lt : k0 < C.gates.length := by
        rw [hk0_def]; split_ifs <;> omega
      have horig : origWire n g (n + k) = n + k0 := by
        unfold origWire; rw [hk0_def]; split_ifs <;> omega
      rw [horig, wireVal_gate n C x k0 hk0_lt hRB]
      simp only [mapGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hru_lt : remap n g r u < n + k := by
        have h1 : remap n g r u ∈ (gateAt (delGate n g r C) k).inputs := by
          rw [delGate_gateAt n g r C hg k hk_lt']
          simp only [mapGate, List.mem_map]
          exact ⟨u, hu, rfl⟩
        exact hAO_rb k hk_lt (remap n g r u) h1
      have hih := ih (remap n g r u) (by omega) (by omega)
      simp only [Function.comp_apply, hih]
      by_cases hug : u = n + g
      · rw [hug, origWire_remap_eq n g r hr, hmatch]
      · rw [origWire_remap_ne n g r u hug]


lemma delGate_correct_of_alias {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {p r : ℕ} (hp : p < C.gates.length) (hr : r < n + p)
    (heq : ∀ x : Fin n → Bool, wireVal n C (n + p) x = wireVal n C r x) :
    circuitFun n (delGate n p r C) = circuitFun n C := by
  funext x
  by_cases hout : C.output < n + C.gates.length
  · have hout' := delGate_output_lt n p r C hp hr hout
    have hv := delGate_wireVal_eq n p r C x hAO.2.1 hp hr (heq x)
      (delGate n p r C).output hout'
    change wireVal n (delGate n p r C) (delGate n p r C).output x =
      wireVal n C C.output x
    rw [hv]
    change wireVal n C (origWire n p (remap n p r C.output)) x = _
    by_cases ho : C.output = n + p
    · rw [ho, origWire_remap_eq n p r hr]
      exact (heq x).symm
    · rw [origWire_remap_ne n p r C.output ho]
  · have hout' : n + (delGate n p r C).gates.length ≤ (delGate n p r C).output := by
      rw [delGate_length n p r C hp]
      change n + (C.gates.length - 1) ≤ remap n p r C.output
      unfold remap
      split_ifs <;> omega
    change Frontier.W n (delGate n p r C) x (delGate n p r C).output =
      Frontier.W n C x C.output
    rw [RootPatch.W_large n _ x _ hout', RootPatch.W_large n _ x _ (by omega)]

lemma least_no_alias {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {p r : ℕ}
    (hp : p < C.gates.length) (hr : r < n + p)
    (heq : ∀ x : Fin n → Bool, Frontier.W n C x (n + p) = Frontier.W n C x r) : False := by
  have hD := delGate_isAO2 n p r C hL.1 hp hr
  have hF : circuitFun n (delGate n p r C) = graphFun G ∅ :=
    (delGate_correct_of_alias hL.1 hp hr heq).trans hL.2.1
  have hsize := hL.2.2 (delGate n p r C) hD hF
  change C.gates.length ≤ (delGate n p r C).gates.length at hsize
  rw [delGate_length n p r C hp] at hsize
  omega

lemma least_projection_wire_raw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (u : Fin n) (w : ℕ)
    (hw : w < n + C.gates.length)
    (hval : ∀ x : Fin n → Bool, Frontier.W n C x w = x u) : w = u.val := by
  by_cases hwn : w < n
  · have htest := hval (fun v => decide (v = u))
    rw [Frontier.W_input n C _ w hwn] at htest
    simp only [decide_true, decide_eq_true_eq] at htest
    exact congrArg Fin.val htest
  · have hp : w - n < C.gates.length := by omega
    have he : n + (w - n) = w := by omega
    apply False.elim
    apply least_no_alias hL hp (show u.val < n + (w - n) by omega)
    intro x
    rw [he, hval x, Frontier.W_input n C x u.val u.isLt]

end NoAlias

namespace SameSideBasis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

-- Section 1: Basic wire, cone, OrReaches, orIn, and side lemmas

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

lemma wval_allTrue {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, wval C (fun _ : Fin n => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · rw [wval_input C _ w hwn]
    · have hj : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      rw [hw_eq]
      have hop := hAO.1 _ (gateAt_mem hj)
      have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
      have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
      have hv0 := ih _ h0 (by omega)
      have hv1 := ih _ h1 (by omega)
      rcases hop with hand | hor
      · rw [wval_gate_and hAO _ hj hand, hv0, hv1]; rfl
      · rw [wval_gate_or hAO _ hj hor, hv0, hv1]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hwn : w < n
    · rw [wval_input C x w hwn] at hwx
      rw [wval_input C y w hwn]
      exact hxy ⟨w, hwn⟩ hwx
    · by_cases hwlen : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hw_eq] at hwx ⊢
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · rw [wval_gate_and hAO x hj hand, Bool.and_eq_true] at hwx
          rw [wval_gate_and hAO y hj hand, Bool.and_eq_true]
          exact ⟨ih _ h0 hwx.1, ih _ h1 hwx.2⟩
        · rw [wval_gate_or hAO x hj hor, Bool.or_eq_true] at hwx
          rw [wval_gate_or hAO y hj hor, Bool.or_eq_true]
          exact hwx.imp (ih _ h0) (ih _ h1)
      · rw [wval_ge_len C x (by omega)] at hwx; cases hwx

-- Cone characterization

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

-- OrReaches and orIn characterization

lemma foldl_orSets_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (orStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_orSets_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (orStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (orStep n acc g).length := by
      simp only [orStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orSets_len]; simp

lemma foldl_orSets_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (orStep n) acc).getD (acc.length + j) [] =
      (acc.length + j) :: (match gs[j].op with
        | GateOp.or =>
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) acc).getD (w - n) [])
        | _ => []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := orStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', orStep, List.length_append, List.length_singleton]; omega
      rw [foldl_orSets_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          acc.length :: (match g.op with
            | GateOp.or =>
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
                (fun w => acc.getD (w - n) [])
            | _ => []) := by
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases g.op <;> rfl
      rw [hlhs]
      congr 1
      cases g.op
      · rfl
      · apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwn : w - n < acc.length := by omega
        have hwn' : w - n < acc'.length := by omega
        rw [foldl_orSets_getD_lt n gs acc' (w - n) hwn']
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      · rfl
      · rfl
      · rfl
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := orStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', orStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma orReaches_lt_len {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  by_contra hge
  unfold OrReaches at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)] at h
  simp at h

lemma orReaches_gate_iff {n : ℕ} {C : Circuit} {j g : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  unfold OrReaches orSets
  have h := foldl_orSets_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [Nat.add_sub_cancel_left, h, ← gateAt_eq hj]
  constructor
  · rintro ⟨_, hmem⟩
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C j).op
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨w, hw, hwg⟩
        rw [List.mem_filter] at hw
        simp only [decide_eq_true_eq] at hw
        exact Or.inr ⟨rfl, w, hw.1, hw.2.1, hw.2.2, ⟨hw.2.1, hwg⟩⟩
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
  · rintro (rfl | ⟨hop, w, hw, hnw, hwnj, hwg⟩)
    · exact ⟨Nat.le_add_right n _, List.mem_cons_self⟩
    · refine ⟨Nat.le_add_right n j, List.mem_cons_of_mem j ?_⟩
      rw [hop, List.mem_flatMap]
      exact ⟨w, List.mem_filter.mpr ⟨hw, by simp [hnw, hwnj]⟩, hwg.2⟩

lemma orReaches_input_false {n : ℕ} {C : Circuit} {w g : ℕ} (hw : w < n) : ¬ OrReaches n C w g :=
  fun h => by have := h.1; omega

lemma orReaches_le {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) : g ≤ w - n := by
  have hnw : n ≤ w := h.1
  have hj : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, hk⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel_left] at hj ⊢
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, _, hnu, hunk, hug⟩
    · exact le_refl _
    · have hlt : u - n < k := by omega
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have := ih (u - n) hlt hug (by omega)
      omega

lemma orReaches_self {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_gate_iff hj).mpr (Or.inl rfl)

lemma orReaches_trans {n : ℕ} {C : Circuit} {w j g : ℕ}
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw : n ≤ w := h1.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h1
    rcases h1 with rfl | ⟨hop, u, hu, hnu, hunk, huj⟩
    · exact h2
    · rw [orReaches_gate_iff hwn]
      refine Or.inr ⟨hop, u, hu, hnu, hunk, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at huj ⊢
      exact ih (u - n) (by omega) huj (by omega)

lemma orReaches_inCone_or_eq {n : ℕ} {C : Circuit} {j g : ℕ} (h : OrReaches n C (n + j) g) :
    g = j ∨ InCone n C g j := by
  have hj := orReaches_lt_len h
  rw [Nat.add_sub_cancel_left] at hj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, hu, hnu, hunj, hug⟩
    · exact Or.inl rfl
    · right
      rw [inCone_iff hj]
      refine ⟨u, hu, hnu, hunj, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      exact ih (u - n) (by omega) hug (by omega)

lemma orReaches_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w g : ℕ} (h : OrReaches n C w g) (hg : gateVal n C g x = true) : wval C x w = true := by
  have hnw : n ≤ w := h.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h
    rcases h with rfl | ⟨hop, u, hu, hnu, hunk, hug⟩
    · exact hg
    · rw [wval_gate_or hAO x hwn hop, Bool.or_eq_true]
      rw [gate_inputs_eq hAO hwn] at hu
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have hvu := ih (u - n) (by omega) hug (by omega)
      rw [← hu_eq] at hvu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hvu
      · exact Or.inr hvu

lemma mem_orIn_input {n : ℕ} (C : Circuit) (u v : Fin n) :
    u ∈ orIn n C v.val ↔ u = v := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (heq | ⟨k, _, hreach, _, _⟩)
    · exact Fin.ext heq
    · exact absurd hreach (orReaches_input_false v.isLt)
  · rintro rfl; exact Or.inl rfl

lemma orIn_and_eq_empty {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  ext u
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
  refine ⟨by have := u.isLt; omega, ?_⟩
  rintro ⟨k, hk, hreach, hor, _⟩
  rw [orReaches_gate_iff hj] at hreach
  rcases hreach with rfl | ⟨hor', _⟩
  · rw [hand] at hor; cases hor
  · rw [hand] at hor'; cases hor'

lemma orIn_or_eq_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  simp only [Finset.mem_union, orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hreach, hork, huk⟩)
    · omega
    · rw [orReaches_gate_iff hj] at hreach
      rcases hreach with rfl | ⟨_, w, hw, hnw, hwnj, hwk⟩
      · rw [gate_inputs_eq hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · rw [gate_inputs_eq hAO hj] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl (Or.inr ⟨k, hk, hwk, hork, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hwk, hork, huk⟩)
  · rintro ((h0 | ⟨k, hk, hwk, hork, huk⟩) | (h1 | ⟨k, hk, hwk, hork, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h0]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 0, opnd_mem hAO hj 0, hwk.1,
        opnd_lt hAO hj 0, hwk⟩), hork, huk⟩
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h1]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 1, opnd_mem hAO hj 1, hwk.1,
        opnd_lt hAO hj 1, hwk⟩), hork, huk⟩

lemma orIn_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) (hx : x u = true) : wval C x w = true := by
  unfold orIn at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with rfl | ⟨k, hk, hreach, hork, huk⟩
  · rw [wval_input C x u.val u.isLt]; exact hx
  · apply orReaches_val_mono hAO x hreach
    rw [gateVal_eq_wval, wval_gate_or hAO x hk hork, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hk] at huk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
    rcases huk with h0 | h1
    · left; rw [← h0, wval_input C x u.val u.isLt]; exact hx
    · right; rw [← h1, wval_input C x u.val u.isLt]; exact hx

lemma orIn_subset_of_orReaches {n : ℕ} {C : Circuit} {w k : ℕ} (h : OrReaches n C w k) :
    orIn n C (n + k) ⊆ orIn n C w := by
  intro u hu
  unfold orIn at hu ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  rcases hu with hu | ⟨m, hm, hkm, horm, hum⟩
  · omega
  · exact Or.inr ⟨m, hm, orReaches_trans h hkm, horm, hum⟩

-- Section 2: Gate deletion and structure from IsLeastAO and IsLiftFixedPoint

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, if_pos hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, if_pos hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [if_neg (by omega), if_neg (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_wval_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (heq : wval C x r = wval C x (n + j)) :
    ∀ w < n + C.gates.length, wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega)
        rw [hdr] at h1
        rw [hdw, h1, heq]
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
          have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          rw [h0, h1, hg]
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
          have h0 := ih (opnd C (w - n - 1 + 1) 0) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n - 1 + 1) 1) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          rw [h0, h1, hg]

lemma delCircuit_wval_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (hle : wval C x (n + j) = true → wval C x r = true) :
    ∀ w < n + C.gates.length, wval C x w = true → wval (delCircuit n C j r) x (delWire n j r w) = true := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hval
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn]; rw [wval_input _ x w hwn] at hval; exact hval
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega) (hle hval)
        rw [hdr] at h1
        rw [hdw]
        exact h1
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]; rw [hw_eq] at hval
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          have h0lt : opnd C (w - n) 0 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega
          have h1lt : opnd C (w - n) 1 < w := by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega
          rcases hAO.1 _ (gateAt_mem (by omega : w - n < C.gates.length)) with hand | hor
          · rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
            rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
            rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
            exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
          · rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
            rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
            rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
            exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]; rw [hw_eq] at hval
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          have h0lt : opnd C (w - n - 1 + 1) 0 < w := by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega
          have h1lt : opnd C (w - n - 1 + 1) 1 < w := by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega
          rcases hAO.1 _ (gateAt_mem (by omega : w - n - 1 + 1 < C.gates.length)) with hand | hor
          · rw [wval_gate_and hAO x (by omega) hand, Bool.and_eq_true] at hval
            rw [wval_gate_and hAO' x hk' (by rw [hg]; exact hand), Bool.and_eq_true]
            rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
            exact ⟨ih _ h0lt (by omega) hval.1, ih _ h1lt (by omega) hval.2⟩
          · rw [wval_gate_or hAO x (by omega) hor, Bool.or_eq_true] at hval
            rw [wval_gate_or hAO' x hk' (by rw [hg]; exact hor), Bool.or_eq_true]
            rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
            exact hval.imp (ih _ h0lt (by omega)) (ih _ h1lt (by omega))

lemma delCircuit_wval_not_inCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ∀ w < n + C.gates.length, w ≠ n + j → (n ≤ w → ¬ InCone n C j (w - n)) →
      wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj hnc
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · have hnc' : ¬ InCone n C j (w - n) := hnc (by omega)
      have hop_ok : ∀ b : Fin 2, opnd C (w - n) b ≠ n + j ∧
          (n ≤ opnd C (w - n) b → ¬ InCone n C j (opnd C (w - n) b - n)) := by
        intro b
        have hk : w - n < C.gates.length := by omega
        have hmem := opnd_mem hAO hk b
        have hlt := opnd_lt hAO hk b
        constructor
        · intro heq; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, by omega, hlt, Or.inl (by omega)⟩
        · intro hnu hin; apply hnc'; rw [inCone_iff hk]
          exact ⟨opnd C (w - n) b, hmem, hnu, hlt, Or.inr hin⟩
      by_cases hlt : w < n + j
      · have hk : w - n < j := by omega
        have hdw : delWire n j r w = n + (w - n) := by
          unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
        rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
        have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (hop_ok 0).1 (hop_ok 0).2
        have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (hop_ok 1).1 (hop_ok 1).2
        rw [h0, h1, hg]
      · have hgt : n + j < w := by omega
        have hk : w - n - 1 < C.gates.length - 1 := by omega
        have hjk : j ≤ w - n - 1 := by omega
        have hdw : delWire n j r w = n + (w - n - 1) := by
          unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
        have hw_eq : w = n + (w - n - 1 + 1) := by omega
        have hidx : w - n = w - n - 1 + 1 := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
        rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
        have h0 := ih (opnd C (w - n - 1 + 1) 0)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by rw [← hidx]; exact (hop_ok 0).1) (by rw [← hidx]; exact (hop_ok 0).2)
        have h1 := ih (opnd C (w - n - 1 + 1) 1)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by rw [← hidx]; exact (hop_ok 1).1) (by rw [← hidx]; exact (hop_ok 1).2)
        rw [h0, h1, hg]

-- GraphFun helpers

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

-- Consequences of IsLeastAO + IsLiftFixedPoint

lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  obtain ⟨u, v, huv⟩ := hne
  have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
    rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
    simp at h1
  · by_contra hge
    push Not at hge
    have h1 := hfun (pairInput u v)
    rw [wval_ge_len C _ hge, (graphFun_pair_iff u v).mpr huv] at h1
    cases h1

lemma least_inOutputCone {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    ∀ j < C.gates.length, InOutputCone n C j := by
  have ⟨u, _, _⟩ := hne
  have hn0 : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) u.isLt
  have hout := output_bounds hL hne
  intro j hj
  refine ⟨hj, ?_⟩
  by_contra hnot
  push Not at hnot
  have hr : 0 < n + j := by omega
  let C' := delCircuit n C j 0
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_not_inCone hL.1 x hj hr C.output hout.2 hnot.1 (fun _ => hnot.2 hout.1)
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj 0] at hsz
  omega

lemma least_no_equiv_wire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ¬ ∀ x : Fin n → Bool, wval C x r = wval C x (n + j) := by
  have hout := output_bounds hL hne
  intro heq
  let C' := delCircuit n C j r
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_eq hL.1 x hj hr (heq x) C.output hout.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj r] at hsz
  omega

lemma least_no_belowF_and_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and) (b : Fin 2) :
    ¬ ∀ x : Fin n → Bool, wval C x (opnd C a b) = true → graphFun G ∅ x = true := by
  have hout := output_bounds hL hne
  intro hbelow
  set r := opnd C a b
  have hr : r < n + a := opnd_lt hL.1 ha b
  let C' := delCircuit n C a r
  have hAO' := delCircuit_isAO2 hL.1 ha hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    cases hFx : graphFun G ∅ x
    · have hrx : wval C x r = false := by
        cases h : wval C x r
        · rfl
        · have := hbelow x h; rw [hFx] at this; cases this
      have hax : wval C x (n + a) = false := by
        rw [wval_gate_and hL.1 x ha hand]
        fin_cases b
        · change wval C x (opnd C a 0) = false at hrx; rw [hrx]; rfl
        · change wval C x (opnd C a 1) = false at hrx; rw [hrx, Bool.and_false]
      have hcx : wval C x C.output = false := by
        change circuitFun n C x = false; rw [congrFun hL.2.1 x]; exact hFx
      change wval (delCircuit n C a r) x (delWire n a r C.output) = false
      rw [delCircuit_wval_eq hL.1 x ha hr (by rw [hrx, hax]) C.output hout.2, hcx]
    · have hcx : wval C x C.output = true := by
        change circuitFun n C x = true; rw [congrFun hL.2.1 x]; exact hFx
      change wval (delCircuit n C a r) x (delWire n a r C.output) = true
      apply delCircuit_wval_ge hL.1 x ha hr _ C.output hout.2 hcx
      intro hax
      rw [wval_gate_and hL.1 x ha hand, Bool.and_eq_true] at hax
      fin_cases b
      · exact hax.1
      · exact hax.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C ha r] at hsz
  omega

lemma input_not_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) :
    ¬ ∀ x : Fin n → Bool, wval C x w = true → graphFun G ∅ x = true := by
  intro h
  have := h (fun i => decide (i = ⟨w, hw⟩)) (by rw [wval_input C _ w hw]; simp)
  rw [graphFun_unit_false] at this
  cases this

lemma lift_no_belowF_orN_opnd {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {h : ℕ} (hh : h < C.gates.length) (hor : (gateAt C h).op = GateOp.or)
    (hnb : ¬ BelowF G C h) (b : Fin 2) :
    ¬ ∀ x : Fin n → Bool, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
  intro hbelow
  apply hLift
  refine ⟨h, hh, b, least_inOutputCone hL hne h hh, hor, hnb, hbelow, ?_⟩
  refine ⟨fun _ => true, wval_allTrue hL.1 (opnd C h b) (by have := opnd_lt hL.1 hh b; omega)⟩

lemma orT_opnds_belowF {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) {h : ℕ} (hh : h < C.gates.length)
    (hor : (gateAt C h).op = GateOp.or) (hb : BelowF G C h) (b : Fin 2) :
    n ≤ opnd C h b ∧ opnd C h b - n < C.gates.length ∧ BelowF G C (opnd C h b - n) := by
  have hwb : ∀ x, wval C x (opnd C h b) = true → graphFun G ∅ x = true := by
    intro x hwx
    apply hb x
    rw [gateVal_eq_wval, wval_gate_or hL.1 x hh hor, Bool.or_eq_true]
    fin_cases b
    · exact Or.inl hwx
    · exact Or.inr hwx
  have hge : n ≤ opnd C h b := by
    by_contra hlt; push Not at hlt; exact input_not_belowF hlt hwb
  have hlt : opnd C h b < n + h := opnd_lt hL.1 hh b
  refine ⟨hge, by omega, ?_⟩
  intro x hx
  apply hwb x
  rw [gateVal_eq_wval] at hx
  rwa [show n + (opnd C h b - n) = opnd C h b by omega] at hx

lemma mem_tops_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ tops G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold tops gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orT_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orT G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold orT gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_orN_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ orN G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.or ∧ ¬ BelowF G C k := by
  letI : DecidableEq GateOp := gateOpDecEq
  unfold orN gatesWhere; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_junk_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {k : ℕ} :
    k ∈ junk G C ↔ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ ¬ BelowF G C k := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty BelowF
  constructor
  · rintro ⟨hk, hand, _, x, hgx, hfx⟩
    refine ⟨hk, hand, fun hb => ?_⟩
    have := hb x hgx; rw [hfx] at this; cases this
  · rintro ⟨hk, hand, hnb⟩
    push Not at hnb
    rcases hnb with ⟨x, hgx, hfx⟩
    refine ⟨hk, hand, hk, x, hgx, ?_⟩
    cases h : graphFun G ∅ x
    · rfl
    · exact absurd h hfx

lemma belowF_reader_is_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {k m : ℕ} (hk : k < C.gates.length) (hbk : BelowF G C k)
    (hm : m < C.gates.length) (hread : n + k ∈ (gateAt C m).inputs) :
    m ∈ orT G C := by
  have hwb : ∀ x, wval C x (n + k) = true → graphFun G ∅ x = true := hbk
  rw [gate_inputs_eq hL.1 hm] at hread
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
  obtain ⟨b, hb⟩ : ∃ b : Fin 2, opnd C m b = n + k := by
    rcases hread with h0 | h1
    · exact ⟨0, h0.symm⟩
    · exact ⟨1, h1.symm⟩
  rcases hL.1.1 _ (gateAt_mem hm) with hand | hor
  · exfalso
    exact least_no_belowF_and_opnd hL hne hm hand b (by rw [hb]; exact hwb)
  · rw [mem_orT_iff]
    refine ⟨hm, hor, ?_⟩
    by_contra hnb
    exact lift_no_belowF_orN_opnd hL hLift hne hm hor hnb b (by rw [hb]; exact hwb)

lemma output_gate_mem_tops_or_orT {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    C.output - n ∈ tops G C ∪ orT G C := by
  have hout := output_bounds hL hne
  have hk : C.output - n < C.gates.length := by omega
  have hb : BelowF G C (C.output - n) := by
    intro x hx
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega] at hx
    rw [← congrFun hL.2.1 x]; exact hx
  rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
  rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
  · exact Or.inl ⟨hk, hand, hb⟩
  · exact Or.inr ⟨hk, hor, hb⟩

lemma exists_reader_of_inCone {n : ℕ} {C : Circuit} {k j : ℕ} (h : InCone n C k j) :
    ∃ m < C.gates.length, n + k ∈ (gateAt C m).inputs := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, hw, hnw, hwnj, rfl | hsub⟩
    · exact ⟨j, hj, by rwa [show n + (w - n) = w by omega]⟩
    · exact ih (w - n) (by omega) hsub

lemma tops_le_orT_add_one {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    (tops G C).card ≤ (orT G C).card + 1 := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  have hdisj : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    rw [mem_tops_iff] at hk1; rw [mem_orT_iff] at hk2
    rw [hk1.2.1] at hk2; cases hk2.2.1
  let S := ((tops G C ∪ orT G C).erase (C.output - n)).image (fun k => n + k)
  let T := (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).image (fun p => opnd C p.1 p.2)
  have hsub : S ⊆ T := by
    intro w hw
    simp only [S, Finset.mem_image, Finset.mem_erase, Finset.mem_union] at hw
    rcases hw with ⟨k, ⟨hne_out, hk_mem⟩, rfl⟩
    have hk_lt : k < C.gates.length := by
      rcases hk_mem with h | h
      · exact (mem_tops_iff.mp h).1
      · exact (mem_orT_iff.mp h).1
    have hk_bf : BelowF G C k := by
      rcases hk_mem with h | h
      · exact (mem_tops_iff.mp h).2.2
      · exact (mem_orT_iff.mp h).2.2
    have hcone := least_inOutputCone hL hne k hk_lt
    have hin : InCone n C k (C.output - n) := by
      rcases hcone.2 with heq | ⟨_, hin⟩
      · exfalso; apply hne_out; omega
      · exact hin
    obtain ⟨m, hm, hread⟩ := exists_reader_of_inCone hin
    have hm_orT := belowF_reader_is_orT hL hLift hne hk_lt hk_bf hm hread
    rw [gate_inputs_eq hL.1 hm] at hread
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hread
    simp only [T, Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true]
    rcases hread with h0 | h1
    · exact ⟨(m, 0), hm_orT, h0.symm⟩
    · exact ⟨(m, 1), hm_orT, h1.symm⟩
  have hcardS : S.card = (tops G C).card + (orT G C).card - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => by omega),
      Finset.card_erase_of_mem hout_mem, Finset.card_union_of_disjoint hdisj]
  have hcardT : T.card ≤ 2 * (orT G C).card := by
    calc T.card ≤ (orT G C ×ˢ (Finset.univ : Finset (Fin 2))).card := Finset.card_image_le
      _ = (orT G C).card * 2 := by simp
      _ = 2 * (orT G C).card := Nat.mul_comm _ _
  have hle := Finset.card_le_card hsub
  rw [hcardS] at hle
  omega

lemma circuit_size_partition {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) :
    C.size = (tops G C).card + (orT G C).card + (junk G C).card + (orN G C).card := by
  have hU : Finset.range C.gates.length = tops G C ∪ orT G C ∪ junk G C ∪ orN G C := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, mem_tops_iff, mem_orT_iff, mem_junk_iff, mem_orN_iff]
    constructor
    · intro hk
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inl ⟨hk, hand, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, hand, hb⟩)
      · by_cases hb : BelowF G C k
        · exact Or.inl (Or.inl (Or.inr ⟨hk, hor, hb⟩))
        · exact Or.inr ⟨hk, hor, hb⟩
    · rintro (((⟨hk, _⟩ | ⟨hk, _⟩) | ⟨hk, _⟩) | ⟨hk, _⟩) <;> exact hk
  have hd1 : Disjoint (tops G C) (orT G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_tops_iff] at h1; rw [mem_orT_iff] at h2; rw [h1.2.1] at h2; cases h2.2.1
  have hd2 : Disjoint (tops G C ∪ orT G C) (junk G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_junk_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff] at h1
    rcases h1 with h1 | h1 <;> exact h2.2.2 h1.2.2
  have hd3 : Disjoint (tops G C ∪ orT G C ∪ junk G C) (orN G C) := by
    rw [Finset.disjoint_left]; intro k h1 h2
    rw [mem_orN_iff] at h2; simp only [Finset.mem_union, mem_tops_iff, mem_orT_iff, mem_junk_iff] at h1
    rcases h1 with (h1 | h1) | h1
    · exact h2.2.2 h1.2.2
    · exact h2.2.2 h1.2.2
    · rw [h1.2.1] at h2; cases h2.2.1
  change C.gates.length = _
  rw [← Finset.card_range C.gates.length, hU,
    Finset.card_union_of_disjoint hd3, Finset.card_union_of_disjoint hd2,
    Finset.card_union_of_disjoint hd1]

lemma circuitFun_iff_exists_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) (x : Fin n → Bool) :
    circuitFun n C x = true ↔ ∃ a ∈ tops G C, gateVal n C a x = true := by
  have hout := output_bounds hL hne
  have hout_mem := output_gate_mem_tops_or_orT hL hne
  constructor
  · intro hcx
    have hkey : ∀ k, k ∈ tops G C ∪ orT G C → gateVal n C k x = true →
        ∃ a ∈ tops G C, gateVal n C a x = true := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hvk
        rw [Finset.mem_union] at hk
        rcases hk with htop | horT
        · exact ⟨k, htop, hvk⟩
        · rw [mem_orT_iff] at horT
          rw [gateVal_eq_wval, wval_gate_or hL.1 x horT.1 horT.2.1, Bool.or_eq_true] at hvk
          rcases hvk with h0 | h1
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 0
            have hlt_k : opnd C k 0 - n < k := by have := opnd_lt hL.1 horT.1 0; omega
            have hmem : opnd C k 0 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 0 - n) = opnd C k 0 by omega]; exact h0)
          · obtain ⟨hge, hlt, hbf⟩ := orT_opnds_belowF hL horT.1 horT.2.1 horT.2.2 1
            have hlt_k : opnd C k 1 - n < k := by have := opnd_lt hL.1 horT.1 1; omega
            have hmem : opnd C k 1 - n ∈ tops G C ∪ orT G C := by
              rw [Finset.mem_union, mem_tops_iff, mem_orT_iff]
              rcases hL.1.1 _ (gateAt_mem hlt) with hand | hor
              · exact Or.inl ⟨hlt, hand, hbf⟩
              · exact Or.inr ⟨hlt, hor, hbf⟩
            exact ih _ hlt_k hmem (by rw [gateVal_eq_wval, show n + (opnd C k 1 - n) = opnd C k 1 by omega]; exact h1)
    apply hkey (C.output - n) hout_mem
    rw [gateVal_eq_wval, show n + (C.output - n) = C.output by omega]
    exact hcx
  · rintro ⟨a, ha, hva⟩
    rw [mem_tops_iff] at ha
    rw [congrFun hL.2.1 x]
    exact ha.2.2 x hva

lemma not_belowF_wval_eq {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {g1 g2 : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g1 ∨ k = g2) :
    ∀ w < n + C.gates.length,
      (∀ k, w = n + k → ¬ BelowF G C k) →
      ∀ x : Fin n → Bool,
        wval C x w = true ↔
          (∃ u ∈ orIn n C w, x u = true) ∨
          (OrReaches n C w g1 ∧ gateVal n C g1 x = true) ∨
          (OrReaches n C w g2 ∧ gateVal n C g2 x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hnb x
    by_cases hwn : w < n
    · constructor
      · intro hwx
        left
        refine ⟨⟨w, hwn⟩, (mem_orIn_input C _ _).mpr rfl, ?_⟩
        rwa [wval_input C x w hwn] at hwx
      · rintro (⟨u, hu, hxu⟩ | ⟨hr, _⟩ | ⟨hr, _⟩)
        · have huw : u = ⟨w, hwn⟩ := (mem_orIn_input C u ⟨w, hwn⟩).mp hu
          subst huw; rw [wval_input C x w hwn]; exact hxu
        · exact absurd hr (orReaches_input_false hwn)
        · exact absurd hr (orReaches_input_false hwn)
    · have hk : w - n < C.gates.length := by omega
      have hw_eq : w = n + (w - n) := by omega
      have hnbk : ¬ BelowF G C (w - n) := hnb (w - n) hw_eq
      rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
      · have hmem : w - n ∈ junk G C := mem_junk_iff.mpr ⟨hk, hand, hnbk⟩
        rw [hjunk] at hmem
        constructor
        · intro hwx
          rcases hmem with h1 | h2
          · right; left
            refine ⟨?_, ?_⟩
            · rw [hw_eq, h1]; exact orReaches_self (by omega)
            · rw [gateVal_eq_wval, ← h1, ← hw_eq]; exact hwx
          · right; right
            refine ⟨?_, ?_⟩
            · rw [hw_eq, h2]; exact orReaches_self (by omega)
            · rw [gateVal_eq_wval, ← h2, ← hw_eq]; exact hwx
        · rintro (⟨u, hu, _⟩ | ⟨hr, hvg⟩ | ⟨hr, hvg⟩)
          · rw [hw_eq, orIn_and_eq_empty hk hand] at hu; simp at hu
          · exact orReaches_val_mono hL.1 x hr hvg
          · exact orReaches_val_mono hL.1 x hr hvg
      · have hop_nb : ∀ b : Fin 2, ∀ m, opnd C (w - n) b = n + m → ¬ BelowF G C m := by
          intro b m hm hbm
          exact lift_no_belowF_orN_opnd hL hLift hne hk hor hnbk b (by rw [hm]; exact hbm)
        have hlt0 : opnd C (w - n) 0 < w := by have := opnd_lt hL.1 hk 0; omega
        have hlt1 : opnd C (w - n) 1 < w := by have := opnd_lt hL.1 hk 1; omega
        have ih0 := ih (opnd C (w - n) 0) hlt0 (by omega) (hop_nb 0) x
        have ih1 := ih (opnd C (w - n) 1) hlt1 (by omega) (hop_nb 1) x
        rw [hw_eq, wval_gate_or hL.1 x hk hor, Bool.or_eq_true, ih0, ih1,
          orIn_or_eq_union hL.1 hk hor]
        have hreach_iff : ∀ g, g = g1 ∨ g = g2 →
            (OrReaches n C (n + (w - n)) g ↔
              OrReaches n C (opnd C (w - n) 0) g ∨ OrReaches n C (opnd C (w - n) 1) g) := by
          intro g hg
          have hne_g : g ≠ w - n := by
            intro heq
            have hgj : g ∈ junk G C := (hjunk g).mpr hg
            rw [heq, mem_junk_iff] at hgj
            rw [hor] at hgj; cases hgj.2.1
          rw [orReaches_gate_iff hk]
          constructor
          · rintro (heq | ⟨_, u, hu, _, _, hug⟩)
            · exact absurd heq hne_g
            · rw [gate_inputs_eq hL.1 hk] at hu
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
              rcases hu with rfl | rfl
              · exact Or.inl hug
              · exact Or.inr hug
          · rintro (h0 | h1)
            · exact Or.inr ⟨hor, opnd C (w - n) 0, opnd_mem hL.1 hk 0, h0.1, opnd_lt hL.1 hk 0, h0⟩
            · exact Or.inr ⟨hor, opnd C (w - n) 1, opnd_mem hL.1 hk 1, h1.1, opnd_lt hL.1 hk 1, h1⟩
        rw [hreach_iff g1 (Or.inl rfl), hreach_iff g2 (Or.inr rfl)]
        constructor
        · rintro ((⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩) | (⟨u, hu, hxu⟩ | ⟨h1, hg1⟩ | ⟨h2, hg2⟩))
          · exact Or.inl ⟨u, Finset.mem_union_left _ hu, hxu⟩
          · exact Or.inr (Or.inl ⟨Or.inl h1, hg1⟩)
          · exact Or.inr (Or.inr ⟨Or.inl h2, hg2⟩)
          · exact Or.inl ⟨u, Finset.mem_union_right _ hu, hxu⟩
          · exact Or.inr (Or.inl ⟨Or.inr h1, hg1⟩)
          · exact Or.inr (Or.inr ⟨Or.inr h2, hg2⟩)
        · rintro (⟨u, hu, hxu⟩ | ⟨h1 | h1, hg1⟩ | ⟨h2 | h2, hg2⟩)
          · rcases Finset.mem_union.mp hu with h0 | h1
            · exact Or.inl (Or.inl ⟨u, h0, hxu⟩)
            · exact Or.inr (Or.inl ⟨u, h1, hxu⟩)
          · exact Or.inl (Or.inr (Or.inl ⟨h1, hg1⟩))
          · exact Or.inr (Or.inr (Or.inl ⟨h1, hg1⟩))
          · exact Or.inl (Or.inr (Or.inr ⟨h2, hg2⟩))
          · exact Or.inr (Or.inr (Or.inr ⟨h2, hg2⟩))


end SameSideBasis


namespace AliasCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

lemma run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

lemma getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

lemma run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

lemma run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

lemma ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

lemma ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

lemma ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (_hs : s < n + gs.length) (_ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma ok_ao {n : ℕ} {gs : List Gate} {w : ℕ} (hok : Ok n gs) : TopForm.IsAO2 n ⟨gs, w⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; exact h2
  · intro j hj i hi
    obtain ⟨o', s', t', h1, h2, h3, h4⟩ := hok j hj
    have e1 : gateAt ⟨gs, w⟩ j = gs[j] := List.getD_eq_getElem _ _ hj
    rw [e1, h1] at hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> assumption
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    obtain ⟨o', s', t', h1, h2, _⟩ := hok i hi
    rw [h1]; rfl

open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def binaryValue (a : Bool) (s t : Bool) : Bool := if a then s && t else s || t

def binaryOp (a : Bool) : GateOp := if a then GateOp.and else GateOp.or

lemma binary_extend {n : ℕ} {gs : List Gate} (hok : Ok n gs)
    (op : Bool) (a b : Option ℕ)
    (ha : ∀ w, a = some w → w < n+gs.length)
    (hb : ∀ w, b = some w → w < n+gs.length) :
    ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs++hs) ∧ hs.length ≤ 1 ∧
      (∀ w, o = some w → w < n+(gs++hs).length) ∧
      ∀ x : Fin n → Bool, ov (gs++hs) (List.ofFn x) o =
        binaryValue op (ov gs (List.ofFn x) a) (ov gs (List.ofFn x) b) := by
  cases op with
  | false =>
    cases a with
    | none =>
      refine ⟨[], b, by simpa using hok, by simp, by simpa using hb, ?_⟩
      intro x
      simp [binaryValue, ov]
    | some s =>
      cases b with
      | none =>
        refine ⟨[], some s, by simpa using hok, by simp, by simpa using ha, ?_⟩
        intro x
        simp [binaryValue, ov]
      | some t =>
        have hs := ha s rfl
        have ht := hb t rfl
        refine ⟨[⟨GateOp.or,[s,t]⟩], some (n+gs.length), ok_snoc hok (Or.inr rfl) hs ht,
          by simp, ?_, ?_⟩
        · intro w hw
          cases hw
          simp
        · intro x
          rw [ov_new gs n _ (by simp) _ s t hs ht]
          simp [binaryValue, ov, GateOp.eval]
  | true =>
    cases a with
    | none =>
      refine ⟨[], none, by simpa using hok, by simp, by simp, ?_⟩
      intro x
      simp [binaryValue, ov]
    | some s =>
      cases b with
      | none =>
        refine ⟨[], none, by simpa using hok, by simp, by simp, ?_⟩
        intro x
        simp [binaryValue, ov]
      | some t =>
        have hs := ha s rfl
        have ht := hb t rfl
        refine ⟨[⟨GateOp.and,[s,t]⟩], some (n+gs.length), ok_snoc hok (Or.inl rfl) hs ht,
          by simp, ?_, ?_⟩
        · intro w hw
          cases hw
          simp
        · intro x
          rw [ov_new gs n _ (by simp) _ s t hs ht]
          simp [binaryValue, ov, GateOp.eval]

def scheduleValue {n : ℕ} (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (j : ℕ) (x : Fin n → Bool) : Bool :=
  match op j with
  | none => match src j with | none => false | some w => V w x
  | some t => binaryValue t (V (a j) x) (V (b j) x)

lemma compile (n : ℕ) (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (hin : ∀ w < n, ∀ x, V w x = (List.ofFn x).getD w false) :
    ∀ p,
      (∀ j < p, op j = none → ∀ w, src j = some w → w < n+j) →
      (∀ j < p, op j ≠ none → a j < n+j ∧ b j < n+j) →
      (∀ j < p, ∀ x, V (n+j) x = scheduleValue V op src a b j x) →
    ∃ (gs : List Gate) (m : ℕ → Option ℕ), Ok n gs ∧
      (∀ w < n+p, (∀ w', m w = some w' → w' < n+gs.length) ∧
        ∀ x : Fin n → Bool, ov gs (List.ofFn x) (m w) = V w x) ∧
      gs.length ≤ ((Finset.range p).filter fun j => op j ≠ none).card := by
  classical
  intro p
  induction p with
  | zero =>
    intro _ _ _
    refine ⟨[], fun w => some w, by intro j hj; simp at hj, ?_, by simp⟩
    intro w hw
    refine ⟨by intro w' h; cases h; simpa using hw, ?_⟩
    intro x
    rw [hin w (by omega) x]
    rfl
  | succ p ih =>
    intro hsrc hab hV
    obtain ⟨gs,m,hok,hm,hsize⟩ := ih (fun j hj => hsrc j (by omega))
      (fun j hj => hab j (by omega)) (fun j hj => hV j (by omega))
    have hstep : ∃ (hs : List Gate) (o : Option ℕ), Ok n (gs++hs) ∧
        (∀ w, o = some w → w < n+(gs++hs).length) ∧
        (∀ x : Fin n → Bool, ov (gs++hs) (List.ofFn x) o = V (n+p) x) ∧
        hs.length ≤ if op p = none then 0 else 1 := by
      cases hop : op p with
      | none =>
        cases hsp : src p with
        | none =>
          refine ⟨[], none, by simpa using hok, by simp, ?_, by simp⟩
          intro x
          rw [hV p (by omega) x]
          simp [scheduleValue,hop,hsp,ov]
        | some w =>
          have hw := hsrc p (by omega) hop w hsp
          obtain ⟨hmb,hme⟩ := hm w hw
          refine ⟨[], m w, by simpa using hok, by simpa using hmb, ?_, by simp⟩
          intro x
          rw [hV p (by omega) x]
          simp only [scheduleValue,hop,hsp,List.append_nil]
          exact hme x
      | some t =>
        have hn : op p ≠ none := by simp [hop]
        obtain ⟨ha,hb⟩ := hab p (by omega) hn
        obtain ⟨hba,hea⟩ := hm (a p) ha
        obtain ⟨hbb,heb⟩ := hm (b p) hb
        obtain ⟨hs,o,hOk,hLen,hBound,hVal⟩ := binary_extend hok t (m (a p)) (m (b p)) hba hbb
        refine ⟨hs,o,hOk,hBound,?_,by simpa [hop] using hLen⟩
        intro x
        rw [hVal x, hea x, heb x, hV p (by omega) x]
        simp [scheduleValue,hop]
    obtain ⟨hs,o,hOk,hBound,hVal,hLen⟩ := hstep
    refine ⟨gs++hs, Function.update m (n+p) o, hOk, ?_, ?_⟩
    · intro w hw
      by_cases hwp : w = n+p
      · subst w
        rw [Function.update_self]
        exact ⟨hBound,hVal⟩
      · rw [Function.update_of_ne hwp]
        obtain ⟨hmb,hme⟩ := hm w (by omega)
        refine ⟨?_, ?_⟩
        · intro w' hw'
          have hlt := hmb w' hw'
          simp only [List.length_append]
          omega
        · intro x
          rw [ov_ext gs hs _ _ (by simpa using hmb), hme x]
    · rw [Finset.range_add_one, Finset.filter_insert, List.length_append]
      simp only [ne_eq] at hsize
      by_cases hp : op p = none
      · simp only [hp, ne_eq, not_true_eq_false, ↓reduceIte] at hLen ⊢
        omega
      · simp only [hp, ne_eq, not_false_eq_true, ↓reduceIte] at hLen ⊢
        rw [Finset.card_insert_of_notMem (by simp)]
        omega

lemma compile_circuit (n : ℕ) (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (hin : ∀ w < n, ∀ x, V w x = (List.ofFn x).getD w false)
    (N : ℕ)
    (hsrc : ∀ j < N, op j = none → ∀ w, src j = some w → w < n+j)
    (hback : ∀ j < N, op j ≠ none → a j < n+j ∧ b j < n+j)
    (hV : ∀ j < N, ∀ x, V (n+j) x = scheduleValue V op src a b j x)
    (out : ℕ) (hout : out < n+N) :
    ∃ C : Circuit, IsAO2 n C ∧
      C.size ≤ ((Finset.range N).filter fun j => op j ≠ none).card ∧
      ∀ x : Fin n → Bool, circuitFun n C x = V out x := by
  obtain ⟨gs,m,hok,hm,hsize⟩ := compile n V op src a b hin N hsrc hback hV
  obtain ⟨_,hsem⟩ := hm out hout
  cases hmo : m out with
  | none =>
    refine ⟨⟨gs,n+gs.length⟩,ok_ao hok,hsize,?_⟩
    intro x
    change (run gs (List.ofFn x)).getD (n+gs.length) false = V out x
    rw [List.getD_eq_default _ _ (by rw [run_length]; simp)]
    have he := hsem x
    simpa only [hmo,ov] using he
  | some w =>
    refine ⟨⟨gs,w⟩,ok_ao hok,hsize,?_⟩
    intro x
    change (run gs (List.ofFn x)).getD w false = V out x
    have he := hsem x
    simpa only [hmo,ov] using he

lemma compile_circuit_shorter (n : ℕ) (V : ℕ → (Fin n → Bool) → Bool)
    (op : ℕ → Option Bool) (src : ℕ → Option ℕ) (a b : ℕ → ℕ)
    (hin : ∀ w < n, ∀ x, V w x = (List.ofFn x).getD w false)
    (N : ℕ)
    (hsrc : ∀ j < N, op j = none → ∀ w, src j = some w → w < n+j)
    (hback : ∀ j < N, op j ≠ none → a j < n+j ∧ b j < n+j)
    (hV : ∀ j < N, ∀ x, V (n+j) x = scheduleValue V op src a b j x)
    (out : ℕ) (hout : out < n+N)
    (hdrop : ∃ j < N, op j = none) :
    ∃ C : Circuit, IsAO2 n C ∧ C.size < N ∧
      ∀ x : Fin n → Bool, circuitFun n C x = V out x := by
  obtain ⟨C,hAO,hsize,hC⟩ := compile_circuit n V op src a b hin N hsrc hback hV out hout
  obtain ⟨j,hj,hno⟩ := hdrop
  have hs : (Finset.range N).filter (fun i => op i ≠ none) ⊆ (Finset.range N).erase j := by
    intro i hi
    obtain ⟨hiN,hiOp⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_erase.mpr
    refine ⟨?_,hiN⟩
    intro he
    subst i
    exact hiOp hno
  have hc := Finset.card_le_card hs
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr hj), Finset.card_range] at hc
  exact ⟨C,hAO,by omega,hC⟩

end AliasCompiler


namespace SameSideSingleton

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm

def setOr {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ a ∈ S, x a = true)

def frontier {n : ℕ} (u v : Fin n) (B D S : Finset (Fin n))
    (α β : Bool) (x : Fin n → Bool) : Bool :=
  setOr S x || (α && (x u && setOr B x)) || (β && (x v && setOr D x))

def leftProxy {n : ℕ} (s : Fin n → Bool) (u v : Fin n) (S : Finset (Fin n))
    (α β : Bool) (x : Fin n → Bool) : Bool :=
  setOr (S.filter fun w => s w = false) x || (α && x u) || (β && x v)

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ a b : Fin n, G.Adj a b ∧ x a = true ∧ x b = true := by
  unfold graphFun
  simp

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (a b : Fin n) : graphFun G ∅ (pairInput a b) = true ↔ G.Adj a b := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨p, q, hpq, hp, hq⟩
    simp only [pairInput, decide_eq_true_eq] at hp hq
    rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
    · exact absurd hpq (G.loopless.irrefl _)
    · exact hpq
    · exact hpq.symm
    · exact absurd hpq (G.loopless.irrefl _)
  · intro hab
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩

lemma setOr_pair {n : ℕ} (S : Finset (Fin n)) (a b : Fin n) :
    setOr S (pairInput a b) = true ↔ a ∈ S ∨ b ∈ S := by
  simp only [setOr, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact Or.inl hp
    · exact Or.inr hp
  · rintro (ha | hb)
    · exact ⟨a, ha, Or.inl rfl⟩
    · exact ⟨b, hb, Or.inr rfl⟩

lemma frontier_of_raw {n : ℕ} {u v : Fin n} {B D S : Finset (Fin n)}
    {α β : Bool} {x : Fin n → Bool} {a : Fin n} (ha : a ∈ S) (hxa : x a = true) :
    frontier u v B D S α β x = true := by
  simp only [frontier, Bool.or_eq_true]
  exact Or.inl (Or.inl (by simp only [setOr, decide_eq_true_eq]; exact ⟨a, ha, hxa⟩))

lemma frontier_of_first {n : ℕ} {u v : Fin n} {B D S : Finset (Fin n)}
    {α β : Bool} {x : Fin n → Bool}
    (hα : α = true) (hu : x u = true) (hB : setOr B x = true) :
    frontier u v B D S α β x = true := by
  simp only [frontier, Bool.or_eq_true, Bool.and_eq_true]
  exact Or.inl (Or.inr ⟨hα, hu, hB⟩)

lemma frontier_of_second {n : ℕ} {u v : Fin n} {B D S : Finset (Fin n)}
    {α β : Bool} {x : Fin n → Bool}
    (hβ : β = true) (hv : x v = true) (hD : setOr D x = true) :
    frontier u v B D S α β x = true := by
  simp only [frontier, Bool.or_eq_true, Bool.and_eq_true]
  exact Or.inr ⟨hβ, hv, hD⟩

lemma frontier_pair {n : ℕ} (s : Fin n → Bool) {u v a b : Fin n}
    {B D S : Finset (Fin n)} {α β : Bool}
    (hu : s u = false) (hv : s v = false) (ha : s a = false) (hb : s b = true)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true) :
    frontier u v B D S α β (pairInput a b) = true ↔
      (a ∈ S ∨ b ∈ S) ∨ (α = true ∧ a = u ∧ b ∈ B) ∨ (β = true ∧ a = v ∧ b ∈ D) := by
  have hub : u ≠ b := by intro h; have := h ▸ hu; simp [hb] at this
  have hvb : v ≠ b := by intro h; have := h ▸ hv; simp [hb] at this
  have haB : a ∉ B := by intro h; have := hB a h; simp [ha] at this
  have haD : a ∉ D := by intro h; have := hD a h; simp [ha] at this
  simp only [frontier, Bool.or_eq_true, Bool.and_eq_true, setOr_pair,
    pairInput, decide_eq_true_eq]
  have hua : u = a ↔ a = u := eq_comm
  have hva : v = a ↔ a = v := eq_comm
  tauto

lemma dirty_singleton_witness {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {u : Fin n} {B : Finset (Fin n)}
    (hbad : ∃ b ∈ B, ¬ G.Adj u b) :
    ∃ x : Fin n → Bool, x u = true ∧ setOr B x = true ∧ graphFun G ∅ x = false := by
  obtain ⟨b, hb, hub⟩ := hbad
  refine ⟨pairInput u b, by simp [pairInput], ?_, ?_⟩
  · exact (setOr_pair B u b).mpr (Or.inr hb)
  · apply Bool.eq_false_iff.mpr
    exact fun hF => hub ((graphFun_pair_iff u b).mp hF)

lemma same_center_simultaneous_dirty {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {u : Fin n} {B D : Finset (Fin n)}
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj u w) :
    ∃ x : Fin n → Bool, x u = true ∧ setOr B x = true ∧ setOr D x = true ∧
      graphFun G ∅ x = false := by
  obtain ⟨b, hb, hub⟩ := hbadB
  obtain ⟨d, hd, hud⟩ := hbadD
  have hbd : ¬ G.Adj b d := fun h => hbip b d h ((hB b hb).trans (hD d hd).symm)
  let x : Fin n → Bool := fun w => decide (w = u ∨ w = b ∨ w = d)
  have hxu : x u = true := by simp [x]
  have hxb : x b = true := by simp [x]
  have hxd : x d = true := by simp [x]
  refine ⟨x, hxu, ?_, ?_, ?_⟩
  · simp only [setOr, decide_eq_true_eq]
    exact ⟨b, hb, hxb⟩
  · simp only [setOr, decide_eq_true_eq]
    exact ⟨d, hd, hxd⟩
  · apply Bool.eq_false_iff.mpr
    intro hf
    obtain ⟨a, c, hac, hxa, hxc⟩ := (graphFun_iff x).mp hf
    simp only [x, decide_eq_true_eq] at hxa hxc
    rcases hxa with rfl | rfl | rfl <;> rcases hxc with rfl | rfl | rfl
    · exact G.loopless.irrefl _ hac
    · exact hub hac
    · exact hud hac
    · exact hub hac.symm
    · exact G.loopless.irrefl _ hac
    · exact hbd hac
    · exact hud hac.symm
    · exact hbd hac.symm
    · exact G.loopless.irrefl _ hac

lemma accepted_pair_has_raw_right {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b) {u v a b : Fin n}
    {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hu : s u = false) (hv : s v = false)
    (ha : s a = false) (hb : s b = true)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true)
    (hS : frontier u v B D S α β (pairInput a b) = true)
    (hT : frontier u v B D T γ δ (pairInput a b) = true) : b ∈ S ∨ b ∈ T := by
  by_cases huv : u ≠ v
  ·
    by_contra h
    push Not at h
    have hs := (frontier_pair s hu hv ha hb hB hD).mp hS
    have ht := (frontier_pair s hu hv ha hb hB hD).mp hT
    by_cases hau : a = u
    · subst a
      have hs' : u ∈ S ∨ α = true := by tauto
      have ht' : u ∈ T ∨ γ = true := by tauto
      obtain ⟨x, hxu, hxB, hxF⟩ := dirty_singleton_witness hbadB
      have hsf : frontier u v B D S α β x = true := by
        rcases hs' with hs' | hs'
        · exact frontier_of_raw hs' hxu
        · exact frontier_of_first hs' hxu hxB
      have htf : frontier u v B D T γ δ x = true := by
        rcases ht' with ht' | ht'
        · exact frontier_of_raw ht' hxu
        · exact frontier_of_first ht' hxu hxB
      have := hclean x hsf htf
      simp [hxF] at this
    · by_cases hav : a = v
      · subst a
        have hs' : v ∈ S ∨ β = true := by tauto
        have ht' : v ∈ T ∨ δ = true := by tauto
        obtain ⟨x, hxv, hxD, hxF⟩ := dirty_singleton_witness hbadD
        have hsf : frontier u v B D S α β x = true := by
          rcases hs' with hs' | hs'
          · exact frontier_of_raw hs' hxv
          · exact frontier_of_second hs' hxv hxD
        have htf : frontier u v B D T γ δ x = true := by
          rcases ht' with ht' | ht'
          · exact frontier_of_raw ht' hxv
          · exact frontier_of_second ht' hxv hxD
        have := hclean x hsf htf
        simp [hxF] at this
      · have hs' : a ∈ S := by tauto
        have ht' : a ∈ T := by tauto
        have hxa : pairInput a a a = true := by simp [pairInput]
        have hF := hclean (pairInput a a) (frontier_of_raw hs' hxa) (frontier_of_raw ht' hxa)
        exact G.loopless.irrefl a ((graphFun_pair_iff a a).mp hF)
  · have huv_eq : u = v := by simpa using huv
    subst v
    by_contra hn
    push Not at hn
    have hs := (frontier_pair s hu hu ha hb hB hD).mp hS
    have ht := (frontier_pair s hu hu ha hb hB hD).mp hT
    by_cases hau : a = u
    · subst a
      obtain ⟨x, hxu, hxB, hxD, hxF⟩ := same_center_simultaneous_dirty s hbip hB hD hbadB hbadD
      have hsf : frontier u u B D S α β x = true := by
        rcases hs with (hsu | hsb) | ⟨hα, _, _⟩ | ⟨hβ, _, _⟩
        · exact frontier_of_raw hsu hxu
        · exact False.elim (hn.1 hsb)
        · exact frontier_of_first hα hxu hxB
        · exact frontier_of_second hβ hxu hxD
      have htf : frontier u u B D T γ δ x = true := by
        rcases ht with (htu | htb) | ⟨hγ, _, _⟩ | ⟨hδ, _, _⟩
        · exact frontier_of_raw htu hxu
        · exact False.elim (hn.2 htb)
        · exact frontier_of_first hγ hxu hxB
        · exact frontier_of_second hδ hxu hxD
      have := hclean x hsf htf
      simp [hxF] at this
    · have hs' : a ∈ S := by tauto
      have ht' : a ∈ T := by tauto
      have hxa : pairInput a a a = true := by simp [pairInput]
      have hF := hclean (pairInput a a) (frontier_of_raw hs' hxa) (frontier_of_raw ht' hxa)
      exact G.loopless.irrefl a ((graphFun_pair_iff a a).mp hF)

lemma clean_frontiers_raw_adj {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {u v : Fin n} {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true)
    {a b : Fin n} (ha : a ∈ S) (hb : b ∈ T) : G.Adj a b := by
  apply (graphFun_pair_iff a b).mp
  exact hclean (pairInput a b) (frontier_of_raw ha (by simp [pairInput]))
    (frontier_of_raw hb (by simp [pairInput]))

lemma clean_frontiers_one_right_empty {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {u v : Fin n} {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true) :
    (S.filter fun w => s w = true) = ∅ ∨ (T.filter fun w => s w = true) = ∅ := by
  by_cases hS : (S.filter fun w => s w = true) = ∅
  · exact Or.inl hS
  · right
    obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    obtain ⟨haS, has⟩ := Finset.mem_filter.mp ha
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    obtain ⟨hbT, hbs⟩ := Finset.mem_filter.mp hb
    exact hbip a b (clean_frontiers_raw_adj hclean haS hbT) (has.trans hbs.symm)

lemma both_right_empty_no_accepted_pair {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b) {u v a b : Fin n}
    {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hu : s u = false) (hv : s v = false)
    (ha : s a = false) (hb : s b = true)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true)
    (hS0 : (S.filter fun w => s w = true) = ∅)
    (hT0 : (T.filter fun w => s w = true) = ∅) :
    ¬ (frontier u v B D S α β (pairInput a b) = true ∧
      frontier u v B D T γ δ (pairInput a b) = true) := by
  rintro ⟨hS, hT⟩
  rcases accepted_pair_has_raw_right s hbip hu hv ha hb hB hD hbadB hbadD hclean hS hT with hs | ht
  · have hmem : b ∈ S.filter (fun w => s w = true) := Finset.mem_filter.mpr ⟨hs, hb⟩
    rw [hS0] at hmem
    exact Finset.notMem_empty _ hmem
  · have hmem : b ∈ T.filter (fun w => s w = true) := Finset.mem_filter.mpr ⟨ht, hb⟩
    rw [hT0] at hmem
    exact Finset.notMem_empty _ hmem

lemma dirty_center_right_filter_adj {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {u r : Fin n} {B : Finset (Fin n)} (hr : s r = true)
    (hB : ∀ w ∈ B, s w = true) (hbad : ∃ b ∈ B, ¬ G.Adj u b)
    (hclean : ∀ x : Fin n → Bool,
      x u = true → setOr B x = true → x r = true → graphFun G ∅ x = true) :
    G.Adj u r := by
  obtain ⟨b, hb, hub⟩ := hbad
  have hbr : ¬ G.Adj b r := fun h => hbip b r h ((hB b hb).trans hr.symm)
  let x : Fin n → Bool := fun w => decide (w = u ∨ w = b ∨ w = r)
  have hxu : x u = true := by simp [x]
  have hxb : x b = true := by simp [x]
  have hxr : x r = true := by simp [x]
  have hF := hclean x hxu
    (by simp only [setOr, decide_eq_true_eq]; exact ⟨b, hb, hxb⟩) hxr
  obtain ⟨a, c, hac, hxa, hxc⟩ := (graphFun_iff x).mp hF
  simp only [x, decide_eq_true_eq] at hxa hxc
  rcases hxa with rfl | rfl | rfl <;> rcases hxc with rfl | rfl | rfl
  · exact False.elim (G.loopless.irrefl _ hac)
  · exact False.elim (hub hac)
  · exact hac
  · exact False.elim (hub hac.symm)
  · exact False.elim (G.loopless.irrefl _ hac)
  · exact False.elim (hbr hac)
  · exact hac.symm
  · exact False.elim (hbr hac.symm)
  · exact False.elim (G.loopless.irrefl _ hac)

lemma projected_frontiers_clean {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {u v : Fin n} {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true) :
    ∀ x : Fin n → Bool, setOr (S.filter fun w => s w = true) x = true →
      leftProxy s u v T γ δ x = true → graphFun G ∅ x = true := by
  intro x hR hL
  simp only [setOr, decide_eq_true_eq] at hR
  obtain ⟨r, hr, hxr⟩ := hR
  obtain ⟨hrS, hrs⟩ := Finset.mem_filter.mp hr
  simp only [leftProxy, Bool.or_eq_true, Bool.and_eq_true] at hL
  apply (graphFun_iff x).mpr
  rcases hL with (hraw | hg) | hh
  · simp only [setOr, decide_eq_true_eq] at hraw
    obtain ⟨a, ha, hxa⟩ := hraw
    exact ⟨r, a, clean_frontiers_raw_adj hclean hrS (Finset.mem_filter.mp ha).1, hxr, hxa⟩
  · have hur : G.Adj u r := dirty_center_right_filter_adj s hbip hrs hB hbadB (by
      intro y hyu hyB hyr
      exact hclean y (frontier_of_raw hrS hyr) (frontier_of_first hg.1 hyu hyB))
    exact ⟨u, r, hur, hg.2, hxr⟩
  · have hvr : G.Adj v r := dirty_center_right_filter_adj s hbip hrs hD hbadD (by
      intro y hyv hyD hyr
      exact hclean y (frontier_of_raw hrS hyr) (frontier_of_second hh.1 hyv hyD))
    exact ⟨v, r, hvr, hh.2, hxr⟩

lemma frontier_le_leftProxy_of_right_empty {n : ℕ} (s : Fin n → Bool)
    {u v : Fin n} {B D T : Finset (Fin n)} {γ δ : Bool}
    (hT0 : (T.filter fun w => s w = true) = ∅) :
    ∀ x : Fin n → Bool, frontier u v B D T γ δ x = true → leftProxy s u v T γ δ x = true := by
  intro x hf
  simp only [frontier, Bool.or_eq_true, Bool.and_eq_true] at hf
  simp only [leftProxy, Bool.or_eq_true, Bool.and_eq_true]
  rcases hf with (hraw | hg) | hh
  · left; left
    simp only [setOr, decide_eq_true_eq] at hraw ⊢
    obtain ⟨a, ha, hxa⟩ := hraw
    have has : s a = false := by
      cases hsa : s a
      · rfl
      · have hmem : a ∈ T.filter (fun w => s w = true) := Finset.mem_filter.mpr ⟨ha, hsa⟩
        rw [hT0] at hmem
        exact False.elim (Finset.notMem_empty _ hmem)
    exact ⟨a, Finset.mem_filter.mpr ⟨ha, has⟩, hxa⟩
  · exact Or.inl (Or.inr ⟨hg.1, hg.2.1⟩)
  · exact Or.inr ⟨hh.1, hh.2.1⟩

lemma projected_frontiers_preserve_accepted_pair {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b) {u v a b : Fin n}
    {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hu : s u = false) (hv : s v = false)
    (ha : s a = false) (hb : s b = true)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true)
    (hT0 : (T.filter fun w => s w = true) = ∅)
    (hS : frontier u v B D S α β (pairInput a b) = true)
    (hT : frontier u v B D T γ δ (pairInput a b) = true) :
    setOr (S.filter fun w => s w = true) (pairInput a b) = true ∧
      leftProxy s u v T γ δ (pairInput a b) = true := by
  refine ⟨?_, frontier_le_leftProxy_of_right_empty s hT0 _ hT⟩
  apply (setOr_pair _ a b).mpr
  right
  rcases accepted_pair_has_raw_right s hbip hu hv ha hb hB hD hbadB hbadD hclean hS hT with hs | ht
  · exact Finset.mem_filter.mpr ⟨hs, hb⟩
  · have hmem : b ∈ T.filter (fun w => s w = true) := Finset.mem_filter.mpr ⟨ht, hb⟩
    rw [hT0] at hmem
    exact False.elim (Finset.notMem_empty _ hmem)

end SameSideSingleton

namespace SameSideSingleton.Build

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Core
open PEqualNP.CleanedNonEdge
open PEqualNP.ReadTwo
open PEqualNP.Outside.L_meta_5012.SameSideBasis

def normal {n : ℕ} (s : Fin n → Bool) (u v : Fin n) (S : Finset (Fin n))
    (α β : Bool) (x : Fin n → Bool) : Bool :=
  if (S.filter fun w => s w = true).Nonempty then setOr (S.filter fun w => s w = true) x
  else leftProxy s u v S α β x

lemma setOr_union {n : ℕ} (S T : Finset (Fin n)) (x : Fin n → Bool) :
    setOr (S ∪ T) x = (setOr S x || setOr T x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [setOr, decide_eq_true_eq, Bool.or_eq_true, Finset.mem_union]
  aesop

lemma leftProxy_union {n : ℕ} (s : Fin n → Bool) (u v : Fin n)
    (S T : Finset (Fin n)) (α β γ δ : Bool) (x : Fin n → Bool) :
    leftProxy s u v (S ∪ T) (α || γ) (β || δ) x =
      (leftProxy s u v S α β x || leftProxy s u v T γ δ x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [leftProxy, Finset.filter_union, setOr_union, Bool.or_eq_true, Bool.and_eq_true]
  tauto

lemma normal_union {n : ℕ} (s : Fin n → Bool) (u v : Fin n)
    (S T : Finset (Fin n)) (α β γ δ : Bool) (x : Fin n → Bool) :
    normal s u v (S ∪ T) (α || γ) (β || δ) x =
      if (S.filter fun w => s w = true).Nonempty then
        if (T.filter fun w => s w = true).Nonempty then
          normal s u v S α β x || normal s u v T γ δ x
        else normal s u v S α β x
      else if (T.filter fun w => s w = true).Nonempty then normal s u v T γ δ x
      else normal s u v S α β x || normal s u v T γ δ x := by
  by_cases hs : (S.filter fun w => s w = true).Nonempty <;>
    by_cases ht : (T.filter fun w => s w = true).Nonempty
  · simp [normal, Finset.filter_union, hs, ht, setOr_union]
  · have ht0 := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [normal, Finset.filter_union, hs, ht, ht0, setOr_union, setOr]
  · have hs0 := Finset.not_nonempty_iff_eq_empty.mp hs
    simp [normal, Finset.filter_union, hs, ht, hs0, setOr_union, setOr]
  · have hs0 := Finset.not_nonempty_iff_eq_empty.mp hs
    have ht0 := Finset.not_nonempty_iff_eq_empty.mp ht
    simp [normal, Finset.filter_union, hs, ht, hs0, ht0, leftProxy_union]

def rightWire {n : ℕ} (s : Fin n → Bool) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  (orIn n C w).filter fun p => s p = true

def proxy {n : ℕ} (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    (w : ℕ) (x : Fin n → Bool) : Bool :=
  normal s u v (orIn n C w) (decide (OrReaches n C w g)) (decide (OrReaches n C w h)) x

lemma orIn_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext a
  exact (mem_orIn_input C a ⟨w, hw⟩).trans Finset.mem_singleton.symm

lemma proxy_input {n : ℕ} (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    proxy s C g h u v w x = x ⟨w, hw⟩ := by
  have hg := orReaches_input_false (g := g) (C := C) hw
  have hh := orReaches_input_false (g := h) (C := C) hw
  cases hs : s ⟨w, hw⟩ <;>
    simp [proxy, normal, orIn_input C w hw, hg, hh, hs, leftProxy, setOr, Finset.filter_singleton]

lemma proxy_first {n : ℕ} (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.and) (hne : g ≠ h)
    (x : Fin n → Bool) : proxy s C g h u v (n + g) x = x u := by
  simp [proxy, normal, orIn_and_eq_empty hg hop, leftProxy, setOr,
    orReaches_gate_iff hg, hop, hne, Ne.symm hne]

lemma proxy_second {n : ℕ} (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    (hh : h < C.gates.length) (hop : (gateAt C h).op = GateOp.and) (hne : g ≠ h)
    (x : Fin n → Bool) : proxy s C g h u v (n + h) x = x v := by
  simp [proxy, normal, orIn_and_eq_empty hh hop, leftProxy, setOr,
    orReaches_gate_iff hh, hop, hne, Ne.symm hne]

lemma reaches_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j k : ℕ}
    (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or) (hne : k ≠ j) :
    OrReaches n C (n + j) k ↔
      OrReaches n C (opnd C j 0) k ∨ OrReaches n C (opnd C j 1) k := by
  rw [orReaches_gate_iff hj]
  constructor
  · rintro (heq | ⟨_, w, hw, _, _, hk⟩)
    · exact False.elim (hne heq)
    · rw [gate_inputs_eq hAO hj] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inl hk
      · exact Or.inr hk
  · rintro (hk | hk)
    · exact Or.inr ⟨hor, opnd C j 0, opnd_mem hAO hj 0, hk.1, opnd_lt hAO hj 0, hk⟩
    · exact Or.inr ⟨hor, opnd C j 1, opnd_mem hAO hj 1, hk.1, opnd_lt hAO hj 1, hk⟩

lemma proxy_or {n : ℕ} (s : Fin n → Bool) {C : Circuit} (hAO : IsAO2 n C)
    (g h : ℕ) (u v : Fin n) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (hgj : g ≠ j) (hhj : h ≠ j)
    (x : Fin n → Bool) :
    proxy s C g h u v (n + j) x =
      if (rightWire s C (opnd C j 0)).Nonempty then
        if (rightWire s C (opnd C j 1)).Nonempty then
          proxy s C g h u v (opnd C j 0) x || proxy s C g h u v (opnd C j 1) x
        else proxy s C g h u v (opnd C j 0) x
      else if (rightWire s C (opnd C j 1)).Nonempty then proxy s C g h u v (opnd C j 1) x
      else proxy s C g h u v (opnd C j 0) x || proxy s C g h u v (opnd C j 1) x := by
  have hflag : ∀ k, k ≠ j → decide (OrReaches n C (n + j) k) =
      (decide (OrReaches n C (opnd C j 0) k) || decide (OrReaches n C (opnd C j 1) k)) := by
    intro k hk
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.or_eq_true]
    exact reaches_or hAO hj hor hk
  unfold proxy
  rw [orIn_or_eq_union hAO hj hor, hflag g hgj, hflag h hhj, normal_union]
  rfl

lemma wire_frontier {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C) (hne : ∃ a b : Fin n, G.Adj a b)
    {g h : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (u v : Fin n) (B D : Finset (Fin n))
    (hg : ∀ x : Fin n → Bool, gateVal n C g x = (x u && setOr B x))
    (hh : ∀ x : Fin n → Bool, gateVal n C h x = (x v && setOr D x))
    {w : ℕ} (hw : w < n + C.gates.length)
    (hnb : ∀ k, w = n + k → ¬ BelowF G C k) (x : Fin n → Bool) :
    wval C x w = frontier u v B D (orIn n C w)
      (decide (OrReaches n C w g)) (decide (OrReaches n C w h)) x := by
  apply Bool.eq_iff_iff.mpr
  rw [not_belowF_wval_eq hL hLift hne hjunk w hw hnb x]
  simp only [frontier, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, hg x, hh x,
    setOr, decide_eq_true_eq]
  exact or_assoc.symm

def topValue {n : ℕ} (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    (j : ℕ) (x : Fin n → Bool) : Bool :=
  if (rightWire s C (opnd C j 0)).Nonempty ∨ (rightWire s C (opnd C j 1)).Nonempty then
    proxy s C g h u v (opnd C j 0) x && proxy s C g h u v (opnd C j 1) x
  else false

def andTag (C : Circuit) (j : ℕ) : Bool :=
  match (gateAt C j).op with
  | GateOp.and => true
  | _ => false

def value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    (w : ℕ) (x : Fin n → Bool) : Bool :=
  if hw : w < n then x ⟨w, hw⟩
  else if BelowF G C (w - n) then
    if andTag C (w - n) then topValue s C g h u v (w - n) x
    else
      (if ha : opnd C (w - n) 0 < w then value G s C g h u v (opnd C (w - n) 0) x else false) ||
      (if hb : opnd C (w - n) 1 < w then value G s C g h u v (opnd C (w - n) 1) x else false)
  else proxy s C g h u v w x
termination_by w

lemma value_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    {w : ℕ} (hw : w < n) (x : Fin n → Bool) :
    value G s C g h u v w x = x ⟨w, hw⟩ := by
  rw [value, dif_pos hw]

lemma value_not_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    {w : ℕ} (hnb : ∀ j, w = n + j → ¬ BelowF G C j) (x : Fin n → Bool) :
    value G s C g h u v w x = proxy s C g h u v w x := by
  by_cases hw : w < n
  · rw [value_input G s C g h u v hw x, proxy_input s C g h u v w hw x]
  · rw [value, dif_neg hw, if_neg (hnb (w - n) (by omega))]

lemma value_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n)
    {j : ℕ} (hbf : BelowF G C j) (hand : (gateAt C j).op = GateOp.and)
    (x : Fin n → Bool) :
    value G s C g h u v (n + j) x = topValue s C g h u v j x := by
  rw [value, dif_neg (by omega), Nat.add_sub_cancel_left, if_pos hbf, if_pos (by simp [andTag, hand])]

lemma value_or_below {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) {C : Circuit} (hAO : IsAO2 n C) (g h : ℕ) (u v : Fin n)
    {j : ℕ} (hj : j < C.gates.length) (hbf : BelowF G C j)
    (hor : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    value G s C g h u v (n + j) x =
      (value G s C g h u v (opnd C j 0) x || value G s C g h u v (opnd C j 1) x) := by
  rw [value, dif_neg (by omega), Nat.add_sub_cancel_left, if_pos hbf,
    if_neg (by simp [andTag, hor]), dif_pos (opnd_lt hAO hj 0), dif_pos (opnd_lt hAO hj 1)]

lemma and_opnd_not_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ a b : Fin n, G.Adj a b)
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (b : Fin 2) :
    ∀ k, opnd C j b = n + k → ¬ BelowF G C k := by
  intro k hk hbf
  apply least_no_belowF_and_opnd hL hne hj hand b
  intro x hx
  apply hbf x
  rw [gateVal_eq_wval, ← hk]
  exact hx

lemma or_opnd_not_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (hne : ∃ a b : Fin n, G.Adj a b)
    {j : ℕ} (hj : j < C.gates.length) (hor : (gateAt C j).op = GateOp.or)
    (hnb : ¬ BelowF G C j) (b : Fin 2) :
    ∀ k, opnd C j b = n + k → ¬ BelowF G C k := by
  intro k hk hbf
  apply lift_no_belowF_orN_opnd hL hLift hne hj hor hnb b
  intro x hx
  apply hbf x
  rw [gateVal_eq_wval, ← hk]
  exact hx

def scheduleOp {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (g h j : ℕ) : Option Bool :=
  if j = g ∨ j = h then none
  else if andTag C j then
    if (rightWire s C (opnd C j 0)).Nonempty ∨ (rightWire s C (opnd C j 1)).Nonempty then some true
    else none
  else if BelowF G C j then some false
  else if (rightWire s C (opnd C j 0)).Nonempty then
    if (rightWire s C (opnd C j 1)).Nonempty then some false else none
  else if (rightWire s C (opnd C j 1)).Nonempty then none else some false

def scheduleSource {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (C : Circuit) (g h : ℕ) (u v : Fin n) (j : ℕ) : Option ℕ :=
  if j = g then some u.val
  else if j = h then some v.val
  else if andTag C j then none
  else if BelowF G C j then none
  else if (rightWire s C (opnd C j 0)).Nonempty then some (opnd C j 0)
  else some (opnd C j 1)

lemma scheduleSource_back {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) {C : Circuit} (hAO : IsAO2 n C)
    (g h : ℕ) (u v : Fin n) {j : ℕ} (hj : j < C.gates.length)
    {w : ℕ} (hw : scheduleSource G s C g h u v j = some w) : w < n + j := by
  unfold scheduleSource at hw
  split_ifs at hw with hgj hhj hA hbf hR
  · cases hw; have := u.isLt; omega
  · cases hw; have := v.isLt; omega
  · cases hw; exact opnd_lt hAO hj 0
  · cases hw; exact opnd_lt hAO hj 1

lemma value_schedule {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (s : Fin n → Bool) {C : Circuit} (hL : IsLeastAO G C)
    (hLift : IsLiftFixedPoint G C) (hne : ∃ a b : Fin n, G.Adj a b)
    {g h : ℕ} (hgh : g ≠ h) (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (u v : Fin n) {j : ℕ} (hj : j < C.gates.length) (x : Fin n → Bool) :
    value G s C g h u v (n + j) x =
      PEqualNP.Outside.L_meta_5012.AliasCompiler.scheduleValue (value G s C g h u v)
        (scheduleOp G s C g h) (scheduleSource G s C g h u v)
        (fun k => opnd C k 0) (fun k => opnd C k 1) j x := by
  have hgJ := (hjunk g).mpr (Or.inl rfl)
  have hhJ := (hjunk h).mpr (Or.inr rfl)
  obtain ⟨hglt, hgop, hgnb⟩ := mem_junk_iff.mp hgJ
  obtain ⟨hhlt, hhop, hhnb⟩ := mem_junk_iff.mp hhJ
  by_cases hgj : j = g
  · subst j
    rw [value_not_below G s C g h u v (fun k hk => (Nat.add_left_cancel hk) ▸ hgnb) x,
      proxy_first s C g h u v hglt hgop hgh x]
    simp [PEqualNP.Outside.L_meta_5012.AliasCompiler.scheduleValue, scheduleOp, scheduleSource,
      value_input G s C g h u v u.isLt x]
  · by_cases hhj : j = h
    · subst j
      rw [value_not_below G s C g h u v (fun k hk => (Nat.add_left_cancel hk) ▸ hhnb) x,
        proxy_second s C g h u v hhlt hhop hgh x]
      simp [PEqualNP.Outside.L_meta_5012.AliasCompiler.scheduleValue, scheduleOp, scheduleSource,
        Ne.symm hgh, value_input G s C g h u v v.isLt x]
    · rcases hL.1.1 _ (gateAt_mem hj) with hand | hor
      · have hbf : BelowF G C j := by
          by_contra hn
          have hjJ := mem_junk_iff.mpr ⟨hj, hand, hn⟩
          rcases (hjunk j).mp hjJ with hg' | hh'
          · exact hgj hg'
          · exact hhj hh'
        have hv0 := value_not_below G s C g h u v (and_opnd_not_below hL hne hj hand 0) x
        have hv1 := value_not_below G s C g h u v (and_opnd_not_below hL hne hj hand 1) x
        rw [value_and G s C g h u v hbf hand x]
        by_cases hR : (rightWire s C (opnd C j 0)).Nonempty ∨ (rightWire s C (opnd C j 1)).Nonempty <;>
          simp [topValue, scheduleOp, scheduleSource, andTag, hand, hgj, hhj, hR,
            PEqualNP.Outside.L_meta_5012.AliasCompiler.scheduleValue,
            PEqualNP.Outside.L_meta_5012.AliasCompiler.binaryValue, hv0, hv1]
      · by_cases hbf : BelowF G C j
        · rw [value_or_below G s hL.1 g h u v hj hbf hor x]
          simp [scheduleOp, scheduleSource, andTag, hor, hgj, hhj, hbf,
            PEqualNP.Outside.L_meta_5012.AliasCompiler.scheduleValue,
            PEqualNP.Outside.L_meta_5012.AliasCompiler.binaryValue]
        · have hv0 := value_not_below G s C g h u v (or_opnd_not_below hL hLift hne hj hor hbf 0) x
          have hv1 := value_not_below G s C g h u v (or_opnd_not_below hL hLift hne hj hor hbf 1) x
          rw [value_not_below G s C g h u v (fun k hk => (Nat.add_left_cancel hk) ▸ hbf) x,
            proxy_or s hL.1 g h u v hj hor (Ne.symm hgj) (Ne.symm hhj) x]
          by_cases hR0 : (rightWire s C (opnd C j 0)).Nonempty <;>
            by_cases hR1 : (rightWire s C (opnd C j 1)).Nonempty <;>
              simp [scheduleOp, scheduleSource, andTag, hor, hgj, hhj, hbf, hR0, hR1,
                PEqualNP.Outside.L_meta_5012.AliasCompiler.scheduleValue,
                PEqualNP.Outside.L_meta_5012.AliasCompiler.binaryValue, hv0, hv1]

def normalTop {n : ℕ} (s : Fin n → Bool) (u v : Fin n)
    (S : Finset (Fin n)) (α β : Bool) (T : Finset (Fin n)) (γ δ : Bool)
    (x : Fin n → Bool) : Bool :=
  if (S.filter fun w => s w = true).Nonempty ∨
      (T.filter fun w => s w = true).Nonempty then
    normal s u v S α β x && normal s u v T γ δ x
  else false

lemma normalTop_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {u v : Fin n} {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true) :
    ∀ x, normalTop s u v S α β T γ δ x = true → graphFun G ∅ x = true := by
  intro x hx
  have hempty := clean_frontiers_one_right_empty s hbip hclean
  by_cases hS : (S.filter fun w => s w = true).Nonempty
  · have hT0 : (T.filter fun w => s w = true) = ∅ := by
      rcases hempty with hS0 | hT0
      · exact False.elim (hS.ne_empty hS0)
      · exact hT0
    have hT : ¬ (T.filter fun w => s w = true).Nonempty := by simp [hT0]
    simp only [normalTop, hS, true_or, ite_true, normal, hT, ite_false,
      Bool.and_eq_true] at hx
    exact projected_frontiers_clean s hbip hB hD hbadB hbadD hclean x hx.1 hx.2
  · by_cases hT : (T.filter fun w => s w = true).Nonempty
    · simp only [normalTop, hS, hT, false_or, ite_true, normal, ite_false,
        Bool.and_eq_true] at hx
      exact projected_frontiers_clean s hbip hB hD hbadB hbadD
        (fun y hyT hyS => hclean y hyS hyT) x hx.2 hx.1
    · simp [normalTop, hS, hT] at hx

lemma normalTop_preserve_accepted_pair {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (s : Fin n → Bool)
    (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {u v a b : Fin n} {B D S T : Finset (Fin n)} {α β γ δ : Bool}
    (hu : s u = false) (hv : s v = false)
    (ha : s a = false) (hb : s b = true)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hclean : ∀ x : Fin n → Bool,
      frontier u v B D S α β x = true → frontier u v B D T γ δ x = true →
      graphFun G ∅ x = true)
    (hSval : frontier u v B D S α β (pairInput a b) = true)
    (hTval : frontier u v B D T γ δ (pairInput a b) = true) :
    normalTop s u v S α β T γ δ (pairInput a b) = true := by
  have hempty := clean_frontiers_one_right_empty s hbip hclean
  by_cases hS : (S.filter fun w => s w = true).Nonempty
  · have hT0 : (T.filter fun w => s w = true) = ∅ := by
      rcases hempty with hS0 | hT0
      · exact False.elim (hS.ne_empty hS0)
      · exact hT0
    have hT : ¬ (T.filter fun w => s w = true).Nonempty := by simp [hT0]
    have hproject := projected_frontiers_preserve_accepted_pair s hbip hu hv ha hb
      hB hD hbadB hbadD hclean hT0 hSval hTval
    simpa only [normalTop, hS, true_or, ite_true, normal, hT, ite_false,
      Bool.and_eq_true] using hproject
  · have hS0 := Finset.not_nonempty_iff_eq_empty.mp hS
    by_cases hT : (T.filter fun w => s w = true).Nonempty
    · have hproject := projected_frontiers_preserve_accepted_pair s hbip hu hv ha hb
        hB hD hbadB hbadD (fun y hyT hyS => hclean y hyS hyT) hS0 hTval hSval
      simpa only [normalTop, hS, hT, false_or, ite_true, normal, ite_false,
        Bool.and_eq_true] using hproject.symm
    · have hT0 := Finset.not_nonempty_iff_eq_empty.mp hT
      exact False.elim (both_right_empty_no_accepted_pair s hbip hu hv ha hb
        hB hD hbadB hbadD hclean hS0 hT0 ⟨hSval, hTval⟩)


lemma compile_value {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (s : Fin n → Bool) {C : Circuit} (hL : IsLeastAO G C)
    (hLift : IsLiftFixedPoint G C) (hne : ∃ a b : Fin n, G.Adj a b)
    {g h : ℕ} (hgh : g ≠ h) (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (u v : Fin n) :
    ∃ E : Circuit, IsAO2 n E ∧ E.size < C.size ∧
      ∀ x : Fin n → Bool, circuitFun n E x = value G s C g h u v C.output x := by
  apply PEqualNP.Outside.L_meta_5012.AliasCompiler.compile_circuit_shorter n
    (value G s C g h u v) (scheduleOp G s C g h) (scheduleSource G s C g h u v)
    (fun k => opnd C k 0) (fun k => opnd C k 1)
  · intro w hw x
    rw [value_input G s C g h u v hw x]
    simp [List.getD_eq_getElem?_getD, hw]
  · intro j hj _ w hw
    exact scheduleSource_back G s hL.1 g h u v hj hw
  · intro j hj _
    exact ⟨opnd_lt hL.1 hj 0, opnd_lt hL.1 hj 1⟩
  · intro j hj x
    exact value_schedule s hL hLift hne hgh hjunk u v hj x
  · exact (output_bounds hL hne).2
  · refine ⟨g, (mem_junk_iff.mp ((hjunk g).mpr (Or.inl rfl))).1, ?_⟩
    simp [scheduleOp]

lemma topValue_semantics {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (hne : ∃ a b : Fin n, G.Adj a b)
    {g h : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (u v : Fin n) (B D : Finset (Fin n))
    (hu : s u = false) (hv : s v = false)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hg : ∀ x : Fin n → Bool, gateVal n C g x = (x u && setOr B x))
    (hh : ∀ x : Fin n → Bool, gateVal n C h x = (x v && setOr D x))
    {j : ℕ} (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbf : BelowF G C j) :
    (∀ x : Fin n → Bool, topValue s C g h u v j x = true → graphFun G ∅ x = true) ∧
    (∀ a b : Fin n, s a = false → s b = true → gateVal n C j (pairInput a b) = true →
      topValue s C g h u v j (pairInput a b) = true) := by
  have heq : ∀ c : Fin 2, ∀ x : Fin n → Bool,
      wval C x (opnd C j c) = frontier u v B D (orIn n C (opnd C j c))
        (decide (OrReaches n C (opnd C j c) g)) (decide (OrReaches n C (opnd C j c) h)) x := by
    intro c x
    apply wire_frontier hL hLift hne hjunk u v B D hg hh
    · have := opnd_lt hL.1 hj c; omega
    · exact and_opnd_not_below hL hne hj hand c
  have hclean : ∀ x : Fin n → Bool,
      frontier u v B D (orIn n C (opnd C j 0))
        (decide (OrReaches n C (opnd C j 0) g)) (decide (OrReaches n C (opnd C j 0) h)) x = true →
      frontier u v B D (orIn n C (opnd C j 1))
        (decide (OrReaches n C (opnd C j 1) g)) (decide (OrReaches n C (opnd C j 1) h)) x = true →
      graphFun G ∅ x = true := by
    intro x hx0 hx1
    apply hbf x
    rw [gateVal_eq_wval, wval_gate_and hL.1 x hj hand, heq 0 x, heq 1 x, Bool.and_eq_true]
    exact ⟨hx0, hx1⟩
  constructor
  · intro x hx
    apply normalTop_clean s hbip hB hD hbadB hbadD hclean x
    unfold normalTop
    unfold topValue proxy rightWire at hx
    split_ifs at hx ⊢ <;> assumption
  · intro a b ha hb hjx
    rw [gateVal_eq_wval, wval_gate_and hL.1 _ hj hand, heq 0 _, heq 1 _, Bool.and_eq_true] at hjx
    have hp := normalTop_preserve_accepted_pair s hbip hu hv ha hb hB hD hbadB hbadD hclean hjx.1 hjx.2
    unfold normalTop at hp
    unfold topValue proxy rightWire
    split_ifs at hp ⊢ <;> assumption

lemma value_clean_semantics {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    (hne : ∃ a b : Fin n, G.Adj a b)
    {g h : ℕ} (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (u v : Fin n) (B D : Finset (Fin n))
    (hu : s u = false) (hv : s v = false)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hbadB : ∃ w ∈ B, ¬ G.Adj u w) (hbadD : ∃ w ∈ D, ¬ G.Adj v w)
    (hg : ∀ x : Fin n → Bool, gateVal n C g x = (x u && setOr B x))
    (hh : ∀ x : Fin n → Bool, gateVal n C h x = (x v && setOr D x)) :
    ∀ j < C.gates.length, BelowF G C j →
    (∀ x : Fin n → Bool, value G s C g h u v (n + j) x = true → graphFun G ∅ x = true) ∧
    (∀ a b : Fin n, s a = false → s b = true → gateVal n C j (pairInput a b) = true →
      value G s C g h u v (n + j) (pairInput a b) = true) := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro hj hbf
    rcases hL.1.1 _ (gateAt_mem hj) with hand | hor
    · have ht := topValue_semantics s hbip hL hLift hne hjunk u v B D hu hv hB hD hbadB hbadD hg hh hj hand hbf
      constructor
      · intro x hx
        rw [value_and G s C g h u v hbf hand x] at hx
        exact ht.1 x hx
      · intro a b ha hb hx
        rw [value_and G s C g h u v hbf hand _]
        exact ht.2 a b ha hb hx
    · have hc := fun b : Fin 2 => orT_opnds_belowF hL hj hor hbf b
      have hclt : ∀ b : Fin 2, opnd C j b - n < j := by
        intro b; have := opnd_lt hL.1 hj b; have := (hc b).1; omega
      have hceq : ∀ b : Fin 2, n + (opnd C j b - n) = opnd C j b := by
        intro b; have := (hc b).1; omega
      have hchild := fun b : Fin 2 => ih (opnd C j b - n) (hclt b) (hc b).2.1 (hc b).2.2
      constructor
      · intro x hx
        rw [value_or_below G s hL.1 g h u v hj hbf hor x, Bool.or_eq_true] at hx
        rcases hx with hx | hx
        · apply (hchild 0).1 x
          simpa only [hceq 0] using hx
        · apply (hchild 1).1 x
          simpa only [hceq 1] using hx
      · intro a b ha hb hx
        rw [gateVal_eq_wval, wval_gate_or hL.1 _ hj hor, Bool.or_eq_true] at hx
        rw [value_or_below G s hL.1 g h u v hj hbf hor _, Bool.or_eq_true]
        rcases hx with hx | hx
        · left
          have hch : gateVal n C (opnd C j 0 - n) (pairInput a b) = true := by
            rw [gateVal_eq_wval, hceq 0]
            exact hx
          simpa only [hceq 0] using (hchild 0).2 a b ha hb hch
        · right
          have hch : gateVal n C (opnd C j 1 - n) (pairInput a b) = true := by
            rw [gateVal_eq_wval, hceq 1]
            exact hx
          simpa only [hceq 1] using (hchild 1).2 a b ha hb hch

lemma dirty_singleton_has_bad_leaf {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} {j : ℕ} {u : Fin n} {B : Finset (Fin n)}
    (hnb : ¬ BelowF G C j)
    (hj : ∀ x : Fin n → Bool, gateVal n C j x = (x u && setOr B x)) :
    ∃ b ∈ B, ¬ G.Adj u b := by
  by_contra hn
  push Not at hn
  apply hnb
  intro x hx
  rw [hj x, Bool.and_eq_true] at hx
  obtain ⟨hxu, hxB⟩ := hx
  simp only [setOr, decide_eq_true_eq] at hxB
  obtain ⟨b, hb, hxb⟩ := hxB
  exact (SameSideSingleton.graphFun_iff x).mpr ⟨u, b, hn b hb, hxu, hxb⟩

lemma least_has_edge_of_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length) :
    ∃ a b : Fin n, G.Adj a b := by
  by_contra hn
  have hadj : ∀ a b : Fin n, ¬ G.Adj a b := fun a b hab => hn ⟨a, b, hab⟩
  let E : Circuit := ⟨[], n⟩
  have hAO : IsAO2 n E := by simp [IsAO2, AndOrOnly, ReadsBack, E]
  have hF : circuitFun n E = graphFun G ∅ := by
    funext x
    have hfalse : graphFun G ∅ x = false := by
      apply Bool.eq_false_iff.mpr
      intro hx
      obtain ⟨a, b, hab, _, _⟩ := (SameSideSingleton.graphFun_iff x).mp hx
      exact hadj a b hab
    rw [hfalse]
    simp [circuitFun, E, Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD]
  have hs := hL.2.2 E hAO hF
  simp only [Circuit.size, E, List.length_nil] at hs
  omega

lemma no_least_same_side_singletons {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (s : Fin n → Bool) (hbip : ∀ a b, G.Adj a b → s a ≠ s b)
    {C : Circuit} (hL : IsLeastAO G C) (hLift : IsLiftFixedPoint G C)
    {g h : ℕ} (hgh : g ≠ h) (hjunk : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (u v : Fin n) (B D : Finset (Fin n))
    (hu : s u = false) (hv : s v = false)
    (hB : ∀ w ∈ B, s w = true) (hD : ∀ w ∈ D, s w = true)
    (hg : ∀ x : Fin n → Bool, gateVal n C g x = (x u && setOr B x))
    (hh : ∀ x : Fin n → Bool, gateVal n C h x = (x v && setOr D x)) : False := by
  obtain ⟨hglt, _, hgnb⟩ := mem_junk_iff.mp ((hjunk g).mpr (Or.inl rfl))
  have hhnb := (mem_junk_iff.mp ((hjunk h).mpr (Or.inr rfl))).2.2
  have hne := least_has_edge_of_gate hL hglt
  have hbadB := dirty_singleton_has_bad_leaf hgnb hg
  have hbadD := dirty_singleton_has_bad_leaf hhnb hh
  obtain ⟨E, hEAO, hEsize, hEval⟩ := compile_value s hL hLift hne hgh hjunk u v
  have hout := output_bounds hL hne
  have houteq : n + (C.output - n) = C.output := by omega
  have houtlt : C.output - n < C.gates.length := by omega
  have houtbf : BelowF G C (C.output - n) := by
    intro x hx
    rw [gateVal_eq_wval, houteq] at hx
    change circuitFun n C x = true at hx
    rwa [hL.2.1] at hx
  have hsem := value_clean_semantics s hbip hL hLift hne hjunk u v B D hu hv
    hB hD hbadB hbadD hg hh (C.output - n) houtlt houtbf
  have hpair : ∀ a b : Fin n, s a = false → s b = true → G.Adj a b →
      circuitFun n E (pairInput a b) = true := by
    intro a b ha hb hab
    rw [hEval (pairInput a b), ← houteq]
    apply hsem.2 a b ha hb
    rw [gateVal_eq_wval, houteq]
    change circuitFun n C (pairInput a b) = true
    rw [hL.2.1]
    exact (SameSideSingleton.graphFun_pair_iff a b).mpr hab
  have hpair_up : ∀ (x : Fin n → Bool) (a b : Fin n), s a = false → s b = true →
      G.Adj a b → x a = true → x b = true → circuitFun n E x = true := by
    intro x a b ha hb hab hxa hxb
    apply wval_mono hEAO (x := pairInput a b) (y := x) ?_ E.output (hpair a b ha hb hab)
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxa
    · exact hxb
  have hEF : circuitFun n E = graphFun G ∅ := by
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      apply hsem.1 x
      rw [houteq, ← hEval x]
      exact hx
    · intro hx
      obtain ⟨a, b, hab, hxa, hxb⟩ := (SameSideSingleton.graphFun_iff x).mp hx
      have hcol := hbip a b hab
      cases ha : s a <;> cases hb : s b
      · exact False.elim (hcol (ha.trans hb.symm))
      · exact hpair_up x a b ha hb hab hxa hxb
      · exact hpair_up x b a hb ha hab.symm hxb hxa
      · exact False.elim (hcol (ha.trans hb.symm))
  have hsize := hL.2.2 E hEAO hEF
  omega

end SameSideSingleton.Build

namespace PrivateProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm
open Frontier

def optionalValue (f : ℕ → Bool) : Option ℕ → Bool
  | none => false
  | some w => f w

def binaryInputs : Option ℕ → Option ℕ → List ℕ
  | some a, some b => [a,b]
  | some a, none => [a,a]
  | none, some b => [b,b]
  | none, none => [0,0]

lemma binaryInputs_length (a b : Option ℕ) : (binaryInputs a b).length = 2 := by
  cases a <;> cases b <;> rfl

lemma binaryInputs_back {a b : Option ℕ} {m : ℕ}
    (hne : a ≠ none ∨ b ≠ none)
    (hback : ∀ w, a = some w ∨ b = some w → w < m) :
    ∀ w ∈ binaryInputs a b, w < m := by
  cases a with
  | none =>
    cases b with
    | none => simp at hne
    | some b =>
      intro w hw
      simp only [binaryInputs, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      subst w
      exact hback b (Or.inr rfl)
  | some a =>
    cases b with
    | none =>
      intro w hw
      simp only [binaryInputs, List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      subst w
      exact hback a (Or.inl rfl)
    | some b =>
      intro w hw
      simp only [binaryInputs, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hback _ (Or.inl rfl)
      · exact hback _ (Or.inr rfl)

lemma binaryInputs_eval (f : ℕ → Bool) {a b : Option ℕ}
    (hne : a ≠ none ∨ b ≠ none) :
    GateOp.or.eval ((binaryInputs a b).map f) = (optionalValue f a || optionalValue f b) := by
  cases a <;> cases b <;> simp_all [binaryInputs, optionalValue, GateOp.eval]

def replacement (C : Circuit) (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (j : Fin C.gates.length) : Gate :=
  if j.val ∈ K then ⟨GateOp.or, binaryInputs (L j.val) (R j.val)⟩ else C.gates[j]

def rewrite (C : Circuit) (K : Finset ℕ) (L R : ℕ → Option ℕ) : Circuit :=
  ⟨List.ofFn (replacement C K L R), C.output⟩

lemma rewrite_length (C : Circuit) (K : Finset ℕ) (L R : ℕ → Option ℕ) :
    (rewrite C K L R).gates.length = C.gates.length := by
  simp [rewrite]

lemma rewrite_size (C : Circuit) (K : Finset ℕ) (L R : ℕ → Option ℕ) :
    (rewrite C K L R).size = C.size := by
  simp [Circuit.size, rewrite_length]

lemma rewrite_gateAt {C : Circuit} (K : Finset ℕ) (L R : ℕ → Option ℕ)
    {j : ℕ} (hj : j < C.gates.length) :
    gateAt (rewrite C K L R) j =
      if j ∈ K then ⟨GateOp.or, binaryInputs (L j) (R j)⟩ else gateAt C j := by
  rw [gateAt_eq _ j (by simpa [rewrite_length] using hj), gateAt_eq C j hj]
  simp [rewrite, replacement]

lemma rewrite_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hne : ∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hback : ∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j) :
    IsAO2 n (rewrite C K L R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change a ∈ List.ofFn (replacement C K L R) at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    by_cases hi : i.val ∈ K
    · simp [replacement, hi]
    · simp only [replacement, hi, ↓reduceIte]
      exact hAO.1 _ (List.getElem_mem i.isLt)
  · intro j hj w hw
    have hjC : j < C.gates.length := by simpa [rewrite_length] using hj
    rw [rewrite_gateAt K L R hjC] at hw
    by_cases hjK : j ∈ K
    · simp only [hjK, ↓reduceIte] at hw
      exact binaryInputs_back (hne j hjC hjK) (hback j hjC hjK) w hw
    · simp only [hjK, ↓reduceIte] at hw
      exact hAO.2.1 j hjC w hw
  · intro a ha
    change a ∈ List.ofFn (replacement C K L R) at ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    by_cases hi : i.val ∈ K
    · simp only [replacement, hi, ↓reduceIte]
      exact binaryInputs_length _ _
    · simp only [replacement, hi, ↓reduceIte]
      exact hAO.2.2 _ (List.getElem_mem i.isLt)

lemma W_gate_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) {j : ℕ} (hj : j < C.gates.length) :
    W n C x (n+j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (W n C x)) := by
  rw [W_gate n C x j hj]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hAO.2.1 j hj w hw)]

def hybrid {n : ℕ} (C : Circuit) (K : Finset ℕ)
    (F : ℕ → (Fin n → Bool) → Bool) (x : Fin n → Bool) (w : ℕ) : Bool :=
  if n ≤ w ∧ w-n ∈ K then F (w-n) x else W n C x w

lemma hybrid_gate {n : ℕ} (C : Circuit) (K : Finset ℕ)
    (F : ℕ → (Fin n → Bool) → Bool) (x : Fin n → Bool) (j : ℕ) :
    hybrid C K F x (n+j) = if j ∈ K then F j x else W n C x (n+j) := by
  simp [hybrid]

lemma hybrid_eq_old {n : ℕ} (C : Circuit) (K : Finset ℕ)
    (F : ℕ → (Fin n → Bool) → Bool) (x : Fin n → Bool) (w : ℕ)
    (hw : w < n ∨ w-n ∉ K) : hybrid C K F x w = W n C x w := by
  apply ite_eq_right
  rintro ⟨hwn, hwK⟩
  rcases hw with h | h
  · omega
  · exact h hwK

lemma rewrite_prefix {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hne : ∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hback : ∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j)
    (g : ℕ) (F : ℕ → (Fin n → Bool) → Bool)
    (hprivate : ∀ j < g, j < C.gates.length → j ∉ K →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w-n ∉ K)
    (hF : ∀ j < C.gates.length, j ∈ K → ∀ x,
      F j x = (optionalValue (hybrid C K F x) (L j) || optionalValue (hybrid C K F x) (R j)))
    (x : Fin n → Bool) (w : ℕ) (hwg : w < n+g) (hwC : w < n+C.gates.length) :
    W n (rewrite C K L R) x w = hybrid C K F x w := by
  have hAO' := rewrite_isAO2 hAO K L R hne hback
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [hybrid_eq_old C K F x w (Or.inl hwn),
        W_input n _ x w hwn, W_input n C x w hwn]
    · have hnw : n ≤ w := by omega
      have hj : w-n < C.gates.length := by omega
      have hjg : w-n < g := by omega
      have he : n+(w-n) = w := by omega
      conv_lhs => rw [← he]
      conv_rhs => rw [← he]
      rw [W_gate_eq hAO' x (by simpa [rewrite_length] using hj),
        rewrite_gateAt K L R hj, hybrid_gate]
      by_cases hjK : w-n ∈ K
      · simp only [hjK, ↓reduceIte]
        rw [binaryInputs_eval (W n (rewrite C K L R) x) (hne _ hj hjK), hF _ hj hjK x]
        have opt : ∀ q : Option ℕ,
            (q = L (w-n) ∨ q = R (w-n)) →
            optionalValue (W n (rewrite C K L R) x) q = optionalValue (hybrid C K F x) q := by
          intro q hq
          cases q with
          | none => rfl
          | some v =>
            have hv : v < n+(w-n) := hback _ hj hjK v (by
              rcases hq with hq | hq
              · exact Or.inl hq.symm
              · exact Or.inr hq.symm)
            exact ih v (by omega) (by omega) (by omega)
        rw [opt _ (Or.inl rfl), opt _ (Or.inr rfl)]
      · simp only [hjK, ↓reduceIte]
        rw [W_gate_eq hAO x hj]
        congr 1
        apply List.map_congr_left
        intro v hv
        have hvw := hAO.2.1 (w-n) hj v hv
        rw [ih v (by omega) (by omega) (by omega)]
        exact hybrid_eq_old C K F x v (hprivate _ hjg hj hjK v hv)

lemma rewrite_op_eq {C : Circuit} (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hK : ∀ j < C.gates.length, j ∈ K → (gateAt C j).op = GateOp.or)
    {j : ℕ} (hj : j < C.gates.length) :
    (gateAt (rewrite C K L R) j).op = (gateAt C j).op := by
  rw [rewrite_gateAt K L R hj]
  by_cases hjK : j ∈ K
  · simp only [hjK, ↓reduceIte]
    exact (hK j hj hjK).symm
  · simp [hjK]

lemma rewrite_mono_prefix {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hne : ∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hback : ∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j)
    (g : ℕ) (F : ℕ → (Fin n → Bool) → Bool)
    (hK : ∀ j ∈ K, j < g)
    (hprivate : ∀ j < g, j < C.gates.length → j ∉ K →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w-n ∉ K)
    (hF : ∀ j < C.gates.length, j ∈ K → ∀ x,
      F j x = (optionalValue (hybrid C K F x) (L j) || optionalValue (hybrid C K F x) (R j)))
    (hFle : ∀ j < C.gates.length, j ∈ K → ∀ x,
      F j x = true → W n C x (n+j) = true)
    (x : Fin n → Bool) (w : ℕ) (hwC : w < n+C.gates.length) :
    W n (rewrite C K L R) x w = true → W n C x w = true := by
  have hAO' := rewrite_isAO2 hAO K L R hne hback
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hval
    by_cases hwn : w < n
    · rw [W_input n _ x w hwn] at hval
      rw [W_input n C x w hwn]
      exact hval
    · have hnw : n ≤ w := by omega
      have hj : w-n < C.gates.length := by omega
      have he : n+(w-n) = w := by omega
      by_cases hjK : w-n ∈ K
      · have hjg := hK (w-n) hjK
        have hv := rewrite_prefix hAO K L R hne hback g F hprivate hF x w (by omega) hwC
        rw [hv] at hval
        have hh : hybrid C K F x w = F (w-n) x := by
          rw [← he, hybrid_gate]
          simp [hjK]
        rw [hh] at hval
        have ht := hFle (w-n) hj hjK x hval
        simpa only [he] using ht
      · rw [← he, W_gate_eq hAO' x (by simpa [rewrite_length] using hj),
          rewrite_gateAt K L R hj, ite_eq_right hjK] at hval
        rw [← he, W_gate_eq hAO x hj]
        have hop := hAO.1 (gateAt C (w-n)) (by rw [gateAt_eq C _ hj]; exact List.getElem_mem hj)
        rcases hop with hop | hop
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hval ⊢
          intro v hv
          have hvw := hAO.2.1 (w-n) hj v hv
          exact ih v (by omega) (by omega) (hval v hv)
        · rw [hop] at hval ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hval ⊢
          obtain ⟨v, hv, hvval⟩ := hval
          have hvw := hAO.2.1 (w-n) hj v hv
          exact ⟨v, hv, ih v (by omega) (by omega) hvval⟩

lemma rewrite_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hne : ∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hback : ∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j)
    (g : ℕ) (F : ℕ → (Fin n → Bool) → Bool)
    (hK : ∀ j ∈ K, j < g)
    (hprivate : ∀ j < g, j < C.gates.length → j ∉ K →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w-n ∉ K)
    (hF : ∀ j < C.gates.length, j ∈ K → ∀ x,
      F j x = (optionalValue (hybrid C K F x) (L j) || optionalValue (hybrid C K F x) (R j)))
    (hFle : ∀ j < C.gates.length, j ∈ K → ∀ x,
      F j x = true → W n C x (n+j) = true)
    (x : Fin n → Bool) (w : ℕ) :
    W n (rewrite C K L R) x w = true → W n C x w = true := by
  by_cases hw : w < n+C.gates.length
  · exact rewrite_mono_prefix hAO K L R hne hback g F hK hprivate hF hFle x w hw
  · have hw' : ((rewrite C K L R).wires (List.ofFn x)).length ≤ w := by
      rw [wires_length, rewrite_length]
      omega
    have hz := getD_ge_length ((rewrite C K L R).wires (List.ofFn x)) w hw'
    change W n (rewrite C K L R) x w = false at hz
    rw [hz]
    exact Bool.false_ne_true.elim

lemma rewrite_eq_outside_prefix {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hne : ∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hback : ∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j)
    (g : ℕ)
    (hprivate : ∀ j < C.gates.length, j ∉ K → j ≠ g →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w-n ∉ K)
    (x : Fin n → Bool)
    (hg : W n (rewrite C K L R) x (n+g) = W n C x (n+g))
    (w : ℕ) (hwC : w < n+C.gates.length) (hwK : w < n ∨ w-n ∉ K) :
    W n (rewrite C K L R) x w = W n C x w := by
  have hAO' := rewrite_isAO2 hAO K L R hne hback
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwn : w < n
    · rw [W_input n _ x w hwn, W_input n C x w hwn]
    · have hnw : n ≤ w := by omega
      have hj : w-n < C.gates.length := by omega
      have hjK : w-n ∉ K := hwK.resolve_left hwn
      have he : n+(w-n) = w := by omega
      by_cases hjg : w-n = g
      · have hwg : w = n+g := by omega
        rw [hwg]
        exact hg
      · conv_lhs => rw [← he]
        conv_rhs => rw [← he]
        rw [W_gate_eq hAO' x (by simpa [rewrite_length] using hj),
          rewrite_gateAt K L R hj, ite_eq_right hjK, W_gate_eq hAO x hj]
        congr 1
        apply List.map_congr_left
        intro v hv
        have hvw := hAO.2.1 (w-n) hj v hv
        exact ih v (by omega) (by omega) (hprivate _ hj hjK hjg v hv)

lemma rewrite_eq_outside {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hne : ∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hback : ∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j)
    (g : ℕ)
    (hprivate : ∀ j < C.gates.length, j ∉ K → j ≠ g →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w-n ∉ K)
    (x : Fin n → Bool)
    (hg : W n (rewrite C K L R) x (n+g) = W n C x (n+g))
    (w : ℕ) (hwK : w < n ∨ w-n ∉ K) :
    W n (rewrite C K L R) x w = W n C x w := by
  by_cases hw : w < n+C.gates.length
  · exact rewrite_eq_outside_prefix hAO K L R hne hback g hprivate x hg w hw hwK
  · have hw0 : (C.wires (List.ofFn x)).length ≤ w := by rw [wires_length]; omega
    have hw1 : ((rewrite C K L R).wires (List.ofFn x)).length ≤ w := by
      rw [wires_length, rewrite_length]; omega
    exact (getD_ge_length _ w hw1).trans (getD_ge_length _ w hw0).symm

def projected {n : ℕ} (S : ℕ → Finset (Fin n)) (T : Finset (Fin n))
    (j : ℕ) (x : Fin n → Bool) : Bool := setOr (S (n+j) ∩ T) x

noncomputable def representative {n : ℕ} (K : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (T : Finset (Fin n)) (w : ℕ) : Option ℕ := by
  classical
  exact if n ≤ w ∧ w-n ∈ K then some w else if S w ⊆ T then some w
    else if h : (S w ∩ T).Nonempty then some (Classical.choose h).val else none

lemma representative_back {n : ℕ} (K : Finset ℕ) (S : ℕ → Finset (Fin n))
    (T : Finset (Fin n)) {w j v : ℕ} (hw : w < n+j)
    (hv : representative K S T w = some v) : v < n+j := by
  classical
  unfold representative at hv
  split at hv
  · cases Option.some.inj hv
    exact hw
  · split at hv
    · cases Option.some.inj hv
      exact hw
    · split at hv
      · have he := Option.some.inj hv
        have hlt := (Classical.choose ‹(S w ∩ T).Nonempty›).isLt
        omega
      · contradiction

lemma representative_nonempty {n : ℕ} (K : Finset ℕ) (S : ℕ → Finset (Fin n))
    (T : Finset (Fin n)) (w : ℕ) (hw : (S w ∩ T).Nonempty) :
    representative K S T w ≠ none := by
  classical
  unfold representative
  split
  · simp
  · split
    · simp
    · simp

lemma representative_value {n : ℕ} (C : Circuit) (K : Finset ℕ)
    (S : ℕ → Finset (Fin n)) (T : Finset (Fin n)) (w : ℕ)
    (hsem : ¬ (n ≤ w ∧ w-n ∈ K) → ∀ x, W n C x w = setOr (S w) x)
    (hsmall : ¬ (n ≤ w ∧ w-n ∈ K) → ¬ S w ⊆ T → (S w ∩ T).card ≤ 1)
    (x : Fin n → Bool) :
    optionalValue (hybrid C K (projected S T) x) (representative K S T w) =
      setOr (S w ∩ T) x := by
  classical
  unfold representative
  split
  next hk =>
    change hybrid C K (projected S T) x w = setOr (S w ∩ T) x
    rw [hybrid, ite_eq_left hk]
    unfold projected
    have he : n+(w-n) = w := by omega
    rw [he]
  next hk =>
    split
    next hgood =>
      simp only [optionalValue, hybrid, hk, ↓reduceIte]
      rw [hsem hk x, Finset.inter_eq_left.mpr hgood]
    next hgood =>
      split
      next hp =>
        let a : Fin n := Classical.choose hp
        have ha : a ∈ S w ∩ T := Classical.choose_spec hp
        have he : S w ∩ T = {a} := by
          ext b
          constructor
          · intro hb
            exact Finset.mem_singleton.mpr ((Finset.card_le_one.mp (hsmall hk hgood)) b hb a ha)
          · intro hb
            rw [Finset.mem_singleton] at hb
            simpa only [hb] using ha
        change hybrid C K (projected S T) x a.val = setOr (S w ∩ T) x
        rw [hybrid_eq_old C K (projected S T) x a.val (Or.inl a.isLt), W_input n C x a.val a.isLt]
        simp [he, setOr]
      next hp =>
        have he : S w ∩ T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hp
        simp [optionalValue, he, setOr]

lemma setOr_union {n : ℕ} (A B : Finset (Fin n)) (x : Fin n → Bool) :
    setOr (A ∪ B) x = (setOr A x || setOr B x) := by
  apply Bool.eq_iff_iff.mpr
  simp only [setOr, decide_eq_true_eq, Finset.mem_union, Bool.or_eq_true]
  constructor
  · rintro ⟨a, ha | ha, hx⟩
    · exact Or.inl ⟨a,ha,hx⟩
    · exact Or.inr ⟨a,ha,hx⟩
  · rintro (⟨a,ha,hx⟩ | ⟨a,ha,hx⟩)
    · exact ⟨a,Or.inl ha,hx⟩
    · exact ⟨a,Or.inr ha,hx⟩

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma projection_data {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (S : ℕ → Finset (Fin n)) (T : Finset (Fin n))
    (hunion : ∀ j < C.gates.length, j ∈ K →
      S (n+j) = S (opnd C j 0) ∪ S (opnd C j 1))
    (hnonempty : ∀ j < C.gates.length, j ∈ K → (S (n+j) ∩ T).Nonempty)
    (hsem : ∀ j < C.gates.length, j ∈ K → ∀ w ∈ (gateAt C j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ K) → ∀ x, W n C x w = setOr (S w) x)
    (hsmall : ∀ j < C.gates.length, j ∈ K → ∀ w ∈ (gateAt C j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ K) → ¬ S w ⊆ T → (S w ∩ T).card ≤ 1) :
    let L := fun j => representative K S T (opnd C j 0)
    let R := fun j => representative K S T (opnd C j 1)
    (∀ j < C.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none) ∧
    (∀ j < C.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j) ∧
    (∀ j < C.gates.length, j ∈ K → ∀ x,
      projected S T j x = (optionalValue (hybrid C K (projected S T) x) (L j) ||
        optionalValue (hybrid C K (projected S T) x) (R j))) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro j hj hjK
    obtain ⟨a, ha⟩ := hnonempty j hj hjK
    rw [hunion j hj hjK] at ha
    obtain ⟨ha, haT⟩ := Finset.mem_inter.mp ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact Or.inl (representative_nonempty K S T _ ⟨a, Finset.mem_inter.mpr ⟨ha,haT⟩⟩)
    · exact Or.inr (representative_nonempty K S T _ ⟨a, Finset.mem_inter.mpr ⟨ha,haT⟩⟩)
  · intro j hj hjK w hw
    rcases hw with hw | hw
    · exact representative_back K S T (hAO.2.1 j hj _ (opnd_mem hAO hj 0)) hw
    · exact representative_back K S T (hAO.2.1 j hj _ (opnd_mem hAO hj 1)) hw
  · intro j hj hjK x
    rw [representative_value C K S T _ (hsem j hj hjK _ (opnd_mem hAO hj 0))
        (hsmall j hj hjK _ (opnd_mem hAO hj 0)) x,
      representative_value C K S T _ (hsem j hj hjK _ (opnd_mem hAO hj 1))
        (hsmall j hj hjK _ (opnd_mem hAO hj 1)) x]
    unfold projected
    rw [hunion j hj hjK]
    have hd : (S (opnd C j 0) ∪ S (opnd C j 1)) ∩ T =
        (S (opnd C j 0) ∩ T) ∪ (S (opnd C j 1) ∩ T) := by
      ext a
      simp only [Finset.mem_inter, Finset.mem_union]
      tauto
    rw [hd, setOr_union]

lemma private_projection_exists {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (K : Finset ℕ) (S : ℕ → Finset (Fin n)) (T : Finset (Fin n)) (g : ℕ)
    (hK : ∀ j ∈ K, j < g)
    (hprivate : ∀ j < g, j < C.gates.length → j ∉ K →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w-n ∉ K)
    (hunion : ∀ j < C.gates.length, j ∈ K →
      S (n+j) = S (opnd C j 0) ∪ S (opnd C j 1))
    (hnonempty : ∀ j < C.gates.length, j ∈ K → (S (n+j) ∩ T).Nonempty)
    (hsemK : ∀ j < C.gates.length, j ∈ K → ∀ x, W n C x (n+j) = setOr (S (n+j)) x)
    (hsem : ∀ j < C.gates.length, j ∈ K → ∀ w ∈ (gateAt C j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ K) → ∀ x, W n C x w = setOr (S w) x)
    (hsmall : ∀ j < C.gates.length, j ∈ K → ∀ w ∈ (gateAt C j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ K) → ¬ S w ⊆ T → (S w ∩ T).card ≤ 1) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size = C.size ∧ D.output = C.output ∧
      (∀ x : Fin n → Bool, ∀ w, w < n+g → w < n+C.gates.length →
        W n D x w = hybrid C K (projected S T) x w) ∧
      (∀ x : Fin n → Bool, ∀ w, W n D x w = true → W n C x w = true) := by
  classical
  let L := fun j => representative K S T (opnd C j 0)
  let R := fun j => representative K S T (opnd C j 1)
  obtain ⟨hN, hB, hF⟩ := projection_data hAO K S T hunion hnonempty hsem hsmall
  have hFle : ∀ j < C.gates.length, j ∈ K → ∀ x,
      projected S T j x = true → W n C x (n+j) = true := by
    intro j hj hjK x hx
    rw [hsemK j hj hjK x]
    exact (setOr_le_iff (S (n+j) ∩ T) (S (n+j))).mpr Finset.inter_subset_left x hx
  refine ⟨rewrite C K L R, rewrite_isAO2 hAO K L R hN hB,
    rewrite_size C K L R, rfl, ?_, ?_⟩
  · exact rewrite_prefix hAO K L R hN hB g (projected S T) hprivate hF
  · exact rewrite_mono hAO K L R hN hB g (projected S T) hK hprivate hF hFle

end PrivateProjection


namespace SingletonPrivacy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier

lemma orReach_comp {n : ℕ} {C : Circuit} {r p q : ℕ}
    (hr : r < C.gates.length) (hrp : OrReaches n C (n + r) p)
    (hpq : OrReaches n C (n + p) q) : OrReaches n C (n + r) q := by
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    have hm : p ∈ (orSets n C).getD r [] := by simpa using hrp.2
    rcases (orSets_mem_iff n C r p hr).mp hm with e | ⟨hop, w, hw, hnw, hwr, hpw⟩
    · subst p
      exact hpq
    · have hpre : OrReaches n C (n + (w - n)) p := by
        exact ⟨by omega, by simpa using hpw⟩
      have hsub := ih (w - n) (by omega) (by omega) hpre
      have he : n + (w - n) = w := by omega
      rw [he] at hsub
      exact orReach_trans n C r hr hop w hw hwr q hsub

lemma orIn_subset_of_reaches {n : ℕ} {C : Circuit} {r p : ℕ}
    (hr : r < C.gates.length) (h : OrReaches n C (n + r) p) :
    orIn n C (n + p) ⊆ orIn n C (n + r) := by
  intro v hv
  rcases (orIn_mem n C (n + p) v).mp hv with hv | ⟨k, hk, hpk, hop, hvin⟩
  · omega
  · exact (orIn_mem n C (n + r) v).mpr
      (Or.inr ⟨k, hk, orReach_comp hr h hpk, hop, hvin⟩)

lemma setOr_orIn_le_W {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) (w : ℕ) (hx : setOr (orIn n C w) x = true) : W n C x w = true := by
  obtain ⟨v, hv, hxv⟩ := of_decide_eq_true hx
  rcases (orIn_mem n C w v).mp hv with h | ⟨k, hk, hwk, hop, hvin⟩
  · rw [← h, W_input n C x v.val v.isLt]
    exact hxv
  · apply reach_up n C x w k hwk
    apply W_or n C x k hk hop v.val hvin (hAO.2.1 k hk v.val hvin)
    rw [W_input n C x v.val v.isLt]
    exact hxv

lemma W_eq_setOr_of_raw {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (w : ℕ) (hraw : ∀ k, k < C.gates.length → OrReaches n C w k →
      (gateAt C k).op = GateOp.or) (x : Fin n → Bool) :
    W n C x w = setOr (orIn n C w) x := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rcases down n C x (fun k hk => gate_op_cases hAO hk) w hx with h | h
    · simpa only [setOr, decide_eq_true_eq] using h
    · obtain ⟨k, hk, hwk, hop, _⟩ := h
      rw [hraw k hk hwk] at hop
      contradiction
  · exact setOr_orIn_le_W hAO x w

lemma bad_descendant_reaches_root {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : circuitFun n C = graphFun G ∅)
    {g h p r : ℕ} (u : Fin n) (hr : r < C.gates.length)
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hgin : (gateAt C g).inputs = [u.val, n + r] ∨
      (gateAt C g).inputs = [n + r, u.val])
    (hlive : ∀ i < C.gates.length,
      C.output = n + i ∨ ∃ j < C.gates.length, n + i ∈ (gateAt C j).inputs)
    (hraw : ∀ v : Fin n, ∃ x,
      gateVal n C p x = true ∧ x v = true ∧ graphFun G ∅ x = false)
    (hg : ∃ x, gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∃ x, gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n C x (opnd C h b) = true → x v = true → graphFun G ∅ x = true)
    (i : ℕ) (hi : i < C.gates.length) (hip : OrReaches n C (n + i) p) :
    OrReaches n C (n + r) i := by
  have hnoh : ∀ b : Fin 2, ¬ OrReaches n C (opnd C h b) p := fun b =>
    not_orReach_of_clean_raw_filter hraw (hhfilter b)
  have hdesc : ∀ d i, C.gates.length - i = d → i < C.gates.length →
      OrReaches n C (n + i) p → OrReaches n C (n + r) i := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro i hdi hi hip
      rcases hlive i hi with hout | ⟨j, hj, hread⟩
      · obtain ⟨x, hpx, _, hFx⟩ := hg
        have hv := reach_up n C x (n + i) p hip hpx
        rw [← hout] at hv
        change circuitFun n C x = true at hv
        rw [hcompute, hFx] at hv
        contradiction
      · have hij := read_index_lt hAO hj hread
        rcases gate_op_cases hAO hj with hand | hor
        · rcases and_reader_is_junk_of_witnesses hAO hTF hJ hj hand hread hip
            hraw hg hh with e | e
          · subst j
            have hir : i = r := by
              rcases hgin with hgin | hgin <;> rw [hgin] at hread <;> simp only
                [List.mem_cons, List.not_mem_nil, or_false] at hread <;> rcases hread with hread | hread <;> omega
            subst i
            exact orReach_self n C r hr
          · subst j
            have hm : n + i = opnd C h 0 ∨ n + i = opnd C h 1 := by
              simpa only [gate_inputs_eq hAO hj, List.mem_cons, List.not_mem_nil, or_false] using hread
            rcases hm with e | e
            · exact False.elim (hnoh 0 (by rw [← e]; exact hip))
            · exact False.elim (hnoh 1 (by rw [← e]; exact hip))
        · have hjp := orReach_trans n C j hj hor (n + i) hread (by omega) p hip
          have hrj := ih (C.gates.length - j) (by omega) j rfl hj hjp
          have hji := orReach_trans n C j hj hor (n + i) hread (by omega) i
            (orReach_self n C i hi)
          exact orReach_comp hr hrj hji
  exact hdesc (C.gates.length - i) i rfl hi hip


def badRegion (n : ℕ) (C : Circuit) (r : ℕ) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range C.gates.length).filter fun p =>
    OrReaches n C (n + r) p ∧ 2 ≤ ((orIn n C (n + p)) ∩ T).card ∧
      ¬ orIn n C (n + p) ⊆ T

lemma mem_badRegion {n : ℕ} {C : Circuit} {r p : ℕ} {T : Finset (Fin n)} :
    p ∈ badRegion n C r T ↔ p < C.gates.length ∧ OrReaches n C (n + r) p ∧
      2 ≤ ((orIn n C (n + p)) ∩ T).card ∧ ¬ orIn n C (n + p) ⊆ T := by
  simp [badRegion]

lemma badRegion_lt_exit {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r g p : ℕ} {T : Finset (Fin n)} (hg : g < C.gates.length)
    (hroot : n + r ∈ (gateAt C g).inputs) (hp : p ∈ badRegion n C r T) : p < g := by
  have hreach := (mem_badRegion.mp hp).2.1
  exact inCone_lt n C g p
    (reach_cone n C g hg (n + r) hroot (hAO.2.1 g hg _ hroot) p hreach)

lemma badRegion_private_of_witnesses {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C)
    (hcompute : circuitFun n C = graphFun G ∅)
    {g h r : ℕ} (u : Fin n) (T : Finset (Fin n)) (hr : r < C.gates.length)
    (hJ : ∀ k ∈ junk G C, k = g ∨ k = h)
    (hgin : (gateAt C g).inputs = [u.val, n + r] ∨
      (gateAt C g).inputs = [n + r, u.val])
    (hlive : ∀ i < C.gates.length,
      C.output = n + i ∨ ∃ j < C.gates.length, n + i ∈ (gateAt C j).inputs)
    (hraw : ∀ p ∈ badRegion n C r T, ∀ v : Fin n, ∃ x,
      gateVal n C p x = true ∧ x v = true ∧ graphFun G ∅ x = false)
    (hg : ∀ p ∈ badRegion n C r T, ∃ x,
      gateVal n C p x = true ∧ gateVal n C g x = true ∧ graphFun G ∅ x = false)
    (hh : ∀ p ∈ badRegion n C r T, ∃ x,
      gateVal n C p x = true ∧ gateVal n C h x = true ∧ graphFun G ∅ x = false)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n C x (opnd C h b) = true → x v = true → graphFun G ∅ x = true) :
    ∀ j, j < C.gates.length → j ∉ badRegion n C r T → j ≠ g →
      ∀ w ∈ (gateAt C j).inputs, w < n ∨ w - n ∉ badRegion n C r T := by
  intro j hj hjK hjg w hw
  by_cases hwn : w < n
  · exact Or.inl hwn
  · right
    intro hpK
    have hn : n ≤ w := by omega
    have hp := (mem_badRegion.mp hpK).1
    have he : n + (w - n) = w := by omega
    have hself : OrReaches n C w (w - n) := by
      simpa only [he] using (orReach_self n C (w - n) hp)
    rcases gate_op_cases hAO hj with hand | hor
    · rcases and_reader_is_junk_of_witnesses hAO hTF hJ hj hand hw hself
        (hraw _ hpK) (hg _ hpK) (hh _ hpK) with e | e
      · exact hjg e
      · subst j
        have hm : w = opnd C h 0 ∨ w = opnd C h 1 := by
          simpa only [gate_inputs_eq hAO hj, List.mem_cons, List.not_mem_nil, or_false] using hw
        rcases hm with e | e
        · exact not_orReach_of_clean_raw_filter (hraw _ hpK) (hhfilter 0)
            (by rw [← e]; exact hself)
        · exact not_orReach_of_clean_raw_filter (hraw _ hpK) (hhfilter 1)
            (by rw [← e]; exact hself)
    · have hjp := orReach_trans n C j hj hor w hw (hAO.2.1 j hj w hw) (w - n) hself
      have hrj := bad_descendant_reaches_root hAO hTF hcompute u hr hJ hgin hlive
        (hraw _ hpK) (hg _ hpK) (hh _ hpK) hhfilter j hj hjp
      have hsub := orIn_subset_of_reaches hj hjp
      have hpdata := (mem_badRegion.mp hpK).2.2
      apply hjK
      apply mem_badRegion.mpr
      refine ⟨hj, hrj, ?_, ?_⟩
      · apply hpdata.1.trans
        apply Finset.card_le_card
        intro a ha
        exact Finset.mem_inter.mpr ⟨hsub (Finset.mem_inter.mp ha).1, (Finset.mem_inter.mp ha).2⟩
      · intro hbad
        exact hpdata.2 (hsub.trans hbad)

lemma no_common_neighbor_of_good_bad {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] (h4 : NoFourCycle G) {u : Fin n} {S T : Finset (Fin n)}
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hgood : 2 ≤ (S ∩ T).card) (hbad : ¬ S ⊆ T) :
    ¬ ∃ v : Fin n, ∀ a ∈ S, G.Adj a v := by
  rintro ⟨v, hv⟩
  have huv : u = v := PreserveEdges.universal_neighbor_unique h4 hgood
    (fun a ha => (hT a).mp (Finset.mem_inter.mp ha).2)
    (fun a ha => (hv a (Finset.mem_inter.mp ha).1).symm)
  apply hbad
  intro a ha
  apply (hT a).mpr
  rw [huv]
  exact (hv a ha).symm

lemma support_dirty_filter_witnesses {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {K : Circuit} {p g h : ℕ} {u : Fin n} {S B C D : Finset (Fin n)}
    (hS : ∀ x, gateVal n K p x = setOr S x)
    (hG : ∀ x, gateVal n K g x = setProduct {u} B x)
    (hH : ∀ x, gateVal n K h x = setProduct C D x)
    (hSB : S ⊆ B) (hno : ¬ ∃ v : Fin n, ∀ a ∈ S, G.Adj a v)
    (hbad : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hSD : ∀ a ∈ S, ∀ d ∈ D, ¬ G.Adj a d) :
    (∀ v : Fin n, ∃ x, gateVal n K p x = true ∧ x v = true ∧ graphFun G ∅ x = false) ∧
    (∃ x, gateVal n K p x = true ∧ gateVal n K g x = true ∧ graphFun G ∅ x = false) ∧
    (∃ x, gateVal n K p x = true ∧ gateVal n K h x = true ∧ graphFun G ∅ x = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    obtain ⟨x, hx, hxv, hFx⟩ := raw_filter_bad_of_no_common_neighbor hno v
    exact ⟨x, by rw [hS]; exact hx, hxv, hFx⟩
  · obtain ⟨x, hx, hxu, hFx⟩ := raw_filter_bad_of_no_common_neighbor hno u
    refine ⟨x, by rw [hS]; exact hx, ?_, hFx⟩
    rw [hG]
    simp only [setProduct, Bool.and_eq_true]
    constructor
    · simp [setOr, hxu]
    · exact (setOr_le_iff S B).mpr hSB x hx
  · obtain ⟨c, hc, d, hd, hcd⟩ := hbad
    obtain ⟨x, hx, hprod, hFx⟩ := OneFlag.raw_product_bad_witness_of_no_common_neighbor
      hno hd hc (fun hdc => hcd hdc.symm) (fun a ha => hSD a ha d hd)
    refine ⟨x, by rw [hS]; exact hx, ?_, hFx⟩
    rw [hH]
    simpa only [setProduct, Bool.and_comm] using hprod


lemma input_reaches_root {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p w : ℕ} (hr : r < C.gates.length) (hp : p < C.gates.length)
    (hrp : OrReaches n C (n + r) p) (hop : (gateAt C p).op = GateOp.or)
    (hw : w ∈ (gateAt C p).inputs) (hwn : n ≤ w) :
    w - n < C.gates.length ∧ OrReaches n C (n + r) (w - n) := by
  have hwp := hAO.2.1 p hp w hw
  have hq : w - n < C.gates.length := by omega
  have he : n + (w - n) = w := by omega
  have hself : OrReaches n C w (w - n) := by
    simpa only [he] using (orReach_self n C (w - n) hq)
  exact ⟨hq, orReach_comp hr hrp (orReach_trans n C p hp hop w hw hwp _ hself)⟩

lemma root_descendant_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p : ℕ} (hr : r < C.gates.length)
    (hrawroot : ∀ k, k < C.gates.length → OrReaches n C (n + r) k →
      (gateAt C k).op = GateOp.or) (hrp : OrReaches n C (n + r) p)
    (x : Fin n → Bool) : W n C x (n + p) = setOr (orIn n C (n + p)) x := by
  apply W_eq_setOr_of_raw hAO
  intro k hk hpk
  exact hrawroot k hk (orReach_comp hr hrp hpk)

lemma root_input_value {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p w : ℕ} (hr : r < C.gates.length) (hp : p < C.gates.length)
    (hrawroot : ∀ k, k < C.gates.length → OrReaches n C (n + r) k →
      (gateAt C k).op = GateOp.or) (hrp : OrReaches n C (n + r) p)
    (hw : w ∈ (gateAt C p).inputs) (x : Fin n → Bool) :
    W n C x w = setOr (orIn n C w) x := by
  apply W_eq_setOr_of_raw hAO
  intro k hk hwk
  have hwn := hwk.1
  have hroot := (input_reaches_root hAO hr hp hrp (hrawroot p hp hrp) hw hwn).2
  have he : n + (w - n) = w := by omega
  apply hrawroot k hk
  apply orReach_comp hr hroot
  simpa only [he] using hwk

lemma orIn_raw_singleton {n : ℕ} (C : Circuit) (v : Fin n) :
    orIn n C v.val = {v} := by
  ext a
  rw [orIn_mem, Finset.mem_singleton]
  constructor
  · rintro (he | ⟨k, hk, hreach, _⟩)
    · exact Fin.ext he
    · have := hreach.1
      omega
  · intro he
    exact Or.inl (congrArg Fin.val he)

lemma badRegion_boundary_small {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p w : ℕ} {T : Finset (Fin n)} (hr : r < C.gates.length)
    (hrawroot : ∀ k, k < C.gates.length → OrReaches n C (n + r) k →
      (gateAt C k).op = GateOp.or) (hpK : p ∈ badRegion n C r T)
    (hw : w ∈ (gateAt C p).inputs) (hout : w < n ∨ w - n ∉ badRegion n C r T)
    (hbad : ¬ orIn n C w ⊆ T) : ((orIn n C w) ∩ T).card ≤ 1 := by
  have hp := (mem_badRegion.mp hpK).1
  have hrp := (mem_badRegion.mp hpK).2.1
  by_cases hwn : w < n
  · have he := orIn_raw_singleton C (⟨w, hwn⟩ : Fin n)
    rw [he]
    exact (Finset.card_le_card Finset.inter_subset_left).trans (by simp)
  · have hn : n ≤ w := by omega
    have hq := input_reaches_root hAO hr hp hrp (hrawroot p hp hrp) hw hn
    have hnK : w - n ∉ badRegion n C r T := hout.resolve_left hwn
    have he : n + (w - n) = w := by omega
    by_contra hcard
    apply hnK
    apply mem_badRegion.mpr
    exact ⟨hq.1, hq.2, by simpa only [he] using (show 2 ≤ ((orIn n C w) ∩ T).card by omega),
      by simpa only [he] using hbad⟩

lemma badRegion_support_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {r p : ℕ} {T : Finset (Fin n)} (hr : r < C.gates.length)
    (hrawroot : ∀ k, k < C.gates.length → OrReaches n C (n + r) k →
      (gateAt C k).op = GateOp.or) (hpK : p ∈ badRegion n C r T) :
    orIn n C (n + p) = orIn n C (opnd C p 0) ∪ orIn n C (opnd C p 1) := by
  have hp := (mem_badRegion.mp hpK).1
  have hrp := (mem_badRegion.mp hpK).2.1
  have hop := hrawroot p hp hrp
  have hin (b : Fin 2) : opnd C p b ∈ (gateAt C p).inputs := by
    rw [gate_inputs_eq hAO hp]
    fin_cases b <;> simp
  have hsem (x : Fin n → Bool) : setOr (orIn n C (n + p)) x =
      (setOr (orIn n C (opnd C p 0)) x || setOr (orIn n C (opnd C p 1)) x) := by
    rw [← root_descendant_value hAO hr hrawroot hrp x, RootPatch.W_gate_eq hAO x hp,
      hop, gate_inputs_eq hAO hp]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
      Bool.or_false, id_eq]
    rw [root_input_value hAO hr hp hrawroot hrp (hin 0) x,
      root_input_value hAO hr hp hrawroot hrp (hin 1) x]
  ext v
  have e := congrArg (fun b : Bool => b = true) (hsem (pairInput v v))
  simp only [Bool.or_eq_true, setOr_pair, or_self] at e
  exact (eq_iff_iff.mp e).trans Finset.mem_union.symm

lemma badRegion_private {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {K : Circuit} (hAO : IsAO2 n K) (hTF : TopForm G K)
    (hcompute : circuitFun n K = graphFun G ∅) (h4 : NoFourCycle G)
    {g h r : ℕ} (u : Fin n) (T B C D : Finset (Fin n)) (hr : r < K.gates.length)
    (hT : ∀ v, v ∈ T ↔ G.Adj u v)
    (hB : B = orIn n K (n + r))
    (hrawroot : ∀ k, k < K.gates.length → OrReaches n K (n + r) k →
      (gateAt K k).op = GateOp.or)
    (hJ : ∀ k ∈ junk G K, k = g ∨ k = h)
    (hgin : (gateAt K g).inputs = [u.val, n + r] ∨
      (gateAt K g).inputs = [n + r, u.val])
    (hlive : ∀ i < K.gates.length,
      K.output = n + i ∨ ∃ j < K.gates.length, n + i ∈ (gateAt K j).inputs)
    (hG : ∀ x, gateVal n K g x = setProduct {u} B x)
    (hH : ∀ x, gateVal n K h x = setProduct C D x)
    (hbad : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n K x (opnd K h b) = true → x v = true → graphFun G ∅ x = true) :
    ∀ j, j < K.gates.length → j ∉ badRegion n K r T → j ≠ g →
      ∀ w ∈ (gateAt K j).inputs, w < n ∨ w - n ∉ badRegion n K r T := by
  have hwitness (p : ℕ) (hpK : p ∈ badRegion n K r T) := by
    have hpdata := mem_badRegion.mp hpK
    have hSB : orIn n K (n + p) ⊆ B := by
      rw [hB]
      exact orIn_subset_of_reaches hr hpdata.2.1
    have hno := no_common_neighbor_of_good_bad h4 hT hpdata.2.2.1 hpdata.2.2.2
    exact support_dirty_filter_witnesses
      (fun x => root_descendant_value hAO hr hrawroot hpdata.2.1 x)
      hG hH hSB hno hbad (fun a ha d hd => hBD a (hSB ha) d hd)
  apply badRegion_private_of_witnesses hAO hTF hcompute u T hr hJ hgin hlive
    (fun p hp => (hwitness p hp).1)
    (fun p hp => (hwitness p hp).2.1)
    (fun p hp => (hwitness p hp).2.2) hhfilter

end SingletonPrivacy

namespace SingletonFlagProjection

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge
open Frontier PrivateProjection SingletonPrivacy

lemma singleton_pair_project {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (u : Fin n) (B T : Finset (Fin n)) (hT : ∀ v, v ∈ T ↔ G.Adj u v)
    (huB : u ∉ B) (a b : Fin n) (hab : G.Adj a b) :
    (pairInput a b u && setOr (B ∩ T) (pairInput a b)) =
      (pairInput a b u && setOr B (pairInput a b)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hu, hBT⟩
    exact ⟨hu, (setOr_le_iff (B ∩ T) B).mpr Finset.inter_subset_left _ hBT⟩
  · rintro ⟨hu, hB⟩
    refine ⟨hu, ?_⟩
    obtain ⟨v, hvB, hv⟩ := of_decide_eq_true hB
    have hpu : u = a ∨ u = b := of_decide_eq_true hu
    have hpv : v = a ∨ v = b := of_decide_eq_true hv
    have huv : u ≠ v := by intro he; subst v; exact huB hvB
    have huvAdj : G.Adj u v := by
      rcases hpu with rfl | rfl <;> rcases hpv with rfl | rfl
      · exact False.elim (huv rfl)
      · exact hab
      · exact hab.symm
      · exact False.elim (huv rfl)
    exact decide_eq_true ⟨v, Finset.mem_inter.mpr ⟨hvB, (hT v).mpr huvAdj⟩, hv⟩

lemma projection_computes {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} (hAO : IsAO2 n D) (hcompute : circuitFun n C = graphFun G ∅)
    (hout : D.output = C.output)
    (hunder : ∀ x w, W n D x w = true → W n C x w = true)
    (hpairs : ∀ a b, G.Adj a b → W n D (pairInput a b) C.output =
      W n C (pairInput a b) C.output) : circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    change W n D x D.output = true at hx
    have hx' : W n D x C.output = true := by simpa only [← hout] using hx
    have hxC := hunder x C.output hx'
    change circuitFun n C x = true at hxC
    simpa only [hcompute] using hxC
  · intro hx
    obtain ⟨a, b, hab, hxa, hxb⟩ := (graphFun_iff x).mp hx
    have hp : W n D (pairInput a b) C.output = true := by
      rw [hpairs a b hab]
      change circuitFun n C (pairInput a b) = true
      rw [hcompute]
      exact (graphFun_pair_iff a b).mpr hab
    have hx' := RootPatch.W_true_mono hAO (pairInput a b) x (by
      intro v hv
      rcases (of_decide_eq_true hv : v = a ∨ v = b) with rfl | rfl
      · exact hxa
      · exact hxb) C.output hp
    change W n D x D.output = true
    rw [hout]
    exact hx'

lemma projection_junk_singleton {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C D : Circuit} {g h : ℕ} (hgh : g ≠ h)
    (hJ : ∀ k, k ∈ junk G C ↔ k = g ∨ k = h)
    (hlen : D.gates.length = C.gates.length)
    (hops : ∀ k, k < C.gates.length → (gateAt D k).op = (gateAt C k).op)
    (hunder : ∀ x w, W n D x w = true → W n C x w = true)
    (hgclean : BelowF G D g)
    (hhretain : ∀ x, gateVal n C h x = true → graphFun G ∅ x = false →
      gateVal n D h x = true) : junk G D = {h} := by
  have hhJ := (hJ h).mpr (Or.inr rfl)
  obtain ⟨_, hhop, hhN, x, hxh, hFx⟩ := Finset.mem_filter.mp hhJ
  apply Finset.ext
  intro k
  simp only [Finset.mem_singleton]
  constructor
  · intro hk
    obtain ⟨hkR, hkop, hkN, y, hyk, hFy⟩ := Finset.mem_filter.mp hk
    have hkC : k < C.gates.length := by omega
    have hkOld : k ∈ junk G C := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hkC, (hops k hkC).symm.trans hkop, hkC, y,
        hunder y (n+k) hyk, hFy⟩
    rcases (hJ k).mp hkOld with rfl | rfl
    · have h := hgclean y hyk
      rw [hFy] at h
      contradiction
    · rfl
  · rintro rfl
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      (hops _ hhN).trans hhop, by omega, x, hhretain x hxh hFx, hFx⟩

lemma singleton_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (u : Fin n) (B : Finset (Fin n)) (hB : ∀ v ∈ B, G.Adj u v)
    (x : Fin n → Bool) (hx : x u && setOr B x = true) : graphFun G ∅ x = true := by
  simp only [Bool.and_eq_true] at hx
  obtain ⟨hxu, hxB⟩ := hx
  obtain ⟨v, hvB, hxv⟩ : ∃ v ∈ B, x v = true := by
    simpa only [setOr, decide_eq_true_eq] using hxB
  exact (graphFun_iff x).mpr ⟨u, v, hB v hvB, hxu, hxv⟩

lemma rewrite_eq_of_not_inCone {n : ℕ} {Q : Circuit} (hAO : IsAO2 n Q)
    (K : Finset ℕ) (L R : ℕ → Option ℕ)
    (hN : ∀ j < Q.gates.length, j ∈ K → L j ≠ none ∨ R j ≠ none)
    (hBack : ∀ j < Q.gates.length, j ∈ K → ∀ w, L j = some w ∨ R j = some w → w < n+j)
    (g : ℕ)
    (hprivate : ∀ j < Q.gates.length, j ∉ K → j ≠ g →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ K)
    (x : Fin n → Bool) (k : ℕ) (hk : k < Q.gates.length) (hkK : k ∉ K)
    (hkg : k ≠ g) (hnc : ¬ InCone n Q g k) :
    W n (rewrite Q K L R) x (n+k) = W n Q x (n+k) := by
  have hAO' := rewrite_isAO2 hAO K L R hN hBack
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [PrivateProjection.W_gate_eq hAO' x (by simpa [rewrite_length] using hk),
      PrivateProjection.W_gate_eq hAO x hk, rewrite_gateAt K L R hk, ite_eq_right hkK]
    congr 1
    apply List.map_congr_left
    intro w hw
    by_cases hwn : w < n
    · rw [W_input n _ x w hwn, W_input n _ x w hwn]
    · have hhigh := hAO.2.1 k hk w hw
      have he : n+(w-n) = w := by omega
      have hne : w-n ≠ g := by
        intro e
        exact hnc ((inCone_iff n Q g k).mpr
          ⟨hk,w-n,by omega,by simpa only [he] using hw,Or.inl e.symm⟩)
      have hnc' : ¬ InCone n Q g (w-n) := by
        intro h
        exact hnc ((inCone_iff n Q g k).mpr
          ⟨hk,w-n,by omega,by simpa only [he] using hw,Or.inr h⟩)
      have hwK : w-n ∉ K := (hprivate k hk hkK hkg w hw).resolve_left hwn
      have hv := ih (w-n) (by omega) (by omega) hwK hne hnc'
      simpa only [he] using hv

lemma private_projection_exists_general {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q)
    {g h r : ℕ} (hgh : g ≠ h) (u : Fin n) (T B : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hprivate : ∀ j, j < Q.gates.length → j ∉ badRegion n Q r T → j ≠ g →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ badRegion n Q r T)
    (hretain : (∀ x, gateVal n Q g x = true → gateVal n Q h x = true →
      graphFun G ∅ x = true) ∨ ¬ InCone n Q g h) :
    ∃ Q' : Circuit, IsLeastAO G Q' ∧ Q'.size = Q.size ∧ junk G Q' = {h} := by
  classical
  have hAO := hL.1
  obtain ⟨_, hgop, hgN, xg, hxg, hxgF⟩ := Finset.mem_filter.mp ((hJ g).mpr (Or.inl rfl))
  obtain ⟨_, hhop, hhN, _⟩ := Finset.mem_filter.mp ((hJ h).mpr (Or.inr rfl))
  have hrootmem : n+r ∈ (gateAt Q g).inputs := by
    rcases hgin with hg | hg <;> rw [hg] <;> simp
  have hrg : r < g := by have := hAO.2.1 g hgN _ hrootmem; omega
  have hrN : r < Q.gates.length := by omega
  have hbadB : ¬ B ⊆ T := by
    intro hsub
    have hx : xg u && setOr B xg = true := by
      rw [hG] at hxg
      simpa [setProduct, setOr] using hxg
    have hf := singleton_clean u B (fun v hv => (hT v).mp (hsub hv)) xg hx
    rw [hxgF] at hf
    contradiction
  let K := badRegion n Q r T
  let S := orIn n Q
  let L := fun j => representative K S T (opnd Q j 0)
  let R := fun j => representative K S T (opnd Q j 1)
  let Q' := rewrite Q K L R
  have hK : ∀ j ∈ K, j < g := fun j hj => badRegion_lt_exit hAO hgN hrootmem hj
  have hrK : r ∈ K := by
    apply mem_badRegion.mpr
    exact ⟨hrN, orReach_self n Q r hrN, by simpa [hB] using hgood,
      by simpa [hB] using hbadB⟩
  have hprivatePre : ∀ j < g, j < Q.gates.length → j ∉ K →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ K := by
    intro j hjg hj hjK
    exact hprivate j hj hjK (by omega)
  have hunion : ∀ j < Q.gates.length, j ∈ K →
      S (n+j) = S (opnd Q j 0) ∪ S (opnd Q j 1) := by
    intro j hj hjK
    exact badRegion_support_union hAO hrN hrawroot hjK
  have hnonempty : ∀ j < Q.gates.length, j ∈ K → (S (n+j) ∩ T).Nonempty := by
    intro j hj hjK
    have hcard := (mem_badRegion.mp hjK).2.2.1
    apply Finset.card_pos.mp
    change 0 < (orIn n Q (n+j) ∩ T).card
    omega
  have hsemK : ∀ j < Q.gates.length, j ∈ K → ∀ x,
      W n Q x (n+j) = setOr (S (n+j)) x := by
    intro j hj hjK x
    exact root_descendant_value hAO hrN hrawroot (mem_badRegion.mp hjK).2.1 x
  have hsem : ∀ j < Q.gates.length, j ∈ K → ∀ w ∈ (gateAt Q j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ K) → ∀ x, W n Q x w = setOr (S w) x := by
    intro j hj hjK w hw hout x
    exact root_input_value hAO hrN hj hrawroot (mem_badRegion.mp hjK).2.1 hw x
  have hsmall : ∀ j < Q.gates.length, j ∈ K → ∀ w ∈ (gateAt Q j).inputs,
      ¬ (n ≤ w ∧ w-n ∈ K) → ¬ S w ⊆ T → (S w ∩ T).card ≤ 1 := by
    intro j hj hjK w hw hout hbad
    exact badRegion_boundary_small hAO hrN hrawroot hjK hw (by
      by_cases hwn : w < n
      · exact Or.inl hwn
      · exact Or.inr (fun hwK => hout ⟨by omega, hwK⟩)) hbad
  obtain ⟨hN,hBack,hF⟩ := projection_data hAO K S T hunion hnonempty hsem hsmall
  have hAO' : IsAO2 n Q' := rewrite_isAO2 hAO K L R hN hBack
  have hlen : Q'.gates.length = Q.gates.length := rewrite_length Q K L R
  have hsize : Q'.size = Q.size := rewrite_size Q K L R
  have hout : Q'.output = Q.output := rfl
  have hprefix := rewrite_prefix hAO K L R hN hBack g (projected S T) hprivatePre hF
  have hunder : ∀ x w, W n Q' x w = true → W n Q x w = true := by
    apply rewrite_mono hAO K L R hN hBack g (projected S T) hK hprivatePre hF
    intro j hj hjK x hx
    rw [hsemK j hj hjK x]
    exact (setOr_le_iff (S (n+j) ∩ T) (S (n+j))).mpr Finset.inter_subset_left x hx
  have hKop : ∀ j ∈ K, (gateAt Q j).op = GateOp.or := by
    intro j hjK
    exact hrawroot j (mem_badRegion.mp hjK).1 (mem_badRegion.mp hjK).2.1
  have hops : ∀ j < Q.gates.length, (gateAt Q' j).op = (gateAt Q j).op := by
    intro j hj
    exact rewrite_op_eq K L R (fun j _ hjK => hKop j hjK) hj
  have hgK : g ∉ K := by intro hgK; have := hK g hgK; omega
  have hhK : h ∉ K := by intro hhK; have := hKop h hhK; rw [hhop] at this; contradiction
  have hgsem : ∀ x, W n Q' x (n+g) = (x u && setOr (B ∩ T) x) := by
    intro x
    rw [PrivateProjection.W_gate_eq hAO' x (by omega), rewrite_gateAt K L R hgN,
      ite_eq_right hgK, hgop]
    have hroot : W n Q' x (n+r) = setOr (B ∩ T) x := by
      rw [hprefix x (n+r) (by omega) (by omega), hybrid_gate, ite_eq_left hrK]
      exact congrArg (fun A => setOr (A ∩ T) x) hB.symm
    rcases hgin with hin | hin
    · rw [hin]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      rw [W_input n Q' x u.val u.isLt, hroot]
    · rw [hin]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        Bool.and_true, id_eq]
      rw [W_input n Q' x u.val u.isLt, hroot, Bool.and_comm]
  have hgclean : BelowF G Q' g := by
    intro x hx
    change W n Q' x (n+g) = true at hx
    rw [hgsem] at hx
    exact singleton_clean u (B ∩ T) (fun v hv => (hT v).mp (Finset.mem_inter.mp hv).2) x hx
  have hgpair : ∀ a b, G.Adj a b → W n Q' (pairInput a b) (n+g) =
      W n Q (pairInput a b) (n+g) := by
    intro a b hab
    rw [hgsem]
    change _ = gateVal n Q g (pairInput a b)
    rw [hG]
    simpa [setProduct, setOr] using singleton_pair_project u B T hT huB a b hab
  have houtK : Q.output < n ∨ Q.output-n ∉ K := by
    by_cases hwn : Q.output < n
    · exact Or.inl hwn
    · right
      intro hoK
      have he : n+(Q.output-n) = Q.output := by omega
      obtain ⟨a, ha⟩ := hnonempty _ (mem_badRegion.mp hoK).1 hoK
      have hval : W n Q (pairInput a a) Q.output = true := by
        rw [← he, hsemK _ (mem_badRegion.mp hoK).1 hoK]
        exact (setOr_pair _ a a).mpr (Or.inl (Finset.mem_inter.mp ha).1)
      change circuitFun n Q (pairInput a a) = true at hval
      rw [hL.2.1] at hval
      exact G.loopless.irrefl a ((graphFun_pair_iff a a).mp hval)
  have hpairs : ∀ a b, G.Adj a b → W n Q' (pairInput a b) Q.output =
      W n Q (pairInput a b) Q.output := by
    intro a b hab
    exact rewrite_eq_outside hAO K L R hN hBack g hprivate (pairInput a b)
      (hgpair a b hab) Q.output houtK
  have hcompute := projection_computes hAO' hL.2.1 hout hunder hpairs
  have hhretain : ∀ x, gateVal n Q h x = true → graphFun G ∅ x = false →
      gateVal n Q' h x = true := by
    intro x hxh hFx
    rcases hretain with hmutual | hind
    ·
      have hg0 : W n Q x (n+g) = false := by
        apply Bool.eq_false_iff.mpr
        intro hxg
        have hF := hmutual x hxg hxh
        rw [hFx] at hF
        contradiction
      have hg0' : W n Q' x (n+g) = false := by
        apply Bool.eq_false_iff.mpr
        intro hxg
        have := hunder x (n+g) hxg
        rw [hg0] at this
        contradiction
      have heq := rewrite_eq_outside hAO K L R hN hBack g hprivate x (hg0'.trans hg0.symm)
        (n+h) (Or.inr (by simpa only [Nat.add_sub_cancel_left] using hhK))
      change W n Q' x (n+h) = true
      rw [heq]
      exact hxh
    · have heq := rewrite_eq_of_not_inCone hAO K L R hN hBack g hprivate x h hhN hhK
        hgh.symm hind
      change W n Q' x (n+h) = true
      rw [heq]
      exact hxh
  have hJnew := projection_junk_singleton hgh hJ hlen hops hunder hgclean hhretain
  refine ⟨Q', ⟨hAO', hcompute, ?_⟩, hsize, hJnew⟩
  intro E hE hEF
  rw [hsize]
  exact hL.2.2 E hE hEF

lemma private_projection_exists {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q)
    {g h r : ℕ} (hgh : g ≠ h) (u : Fin n) (T B : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hprivate : ∀ j, j < Q.gates.length → j ∉ badRegion n Q r T → j ≠ g →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ badRegion n Q r T)
    (hmutual : ∀ x, gateVal n Q g x = true → gateVal n Q h x = true →
      graphFun G ∅ x = true) :
    ∃ Q' : Circuit, IsLeastAO G Q' ∧ Q'.size = Q.size ∧ junk G Q' = {h} := by
  exact private_projection_exists_general hL hgh u T B hT hB huB hgood hrawroot
    hJ hgin hG hprivate (Or.inl hmutual)

lemma private_projection_exists_independent {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q)
    {g h r : ℕ} (hgh : g ≠ h) (u : Fin n) (T B : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hprivate : ∀ j, j < Q.gates.length → j ∉ badRegion n Q r T → j ≠ g →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ badRegion n Q r T)
    (hind : ¬ InCone n Q g h) :
    ∃ Q' : Circuit, IsLeastAO G Q' ∧ Q'.size = Q.size ∧ junk G Q' = {h} := by
  exact private_projection_exists_general hL hgh u T B hT hB huB hgood hrawroot
    hJ hgin hG hprivate (Or.inr hind)

lemma singleton_flag_projection_exists {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q) (hTF : TopForm G Q)
    (h4 : NoFourCycle G) {g h r : ℕ} (hgh : g ≠ h) (u : Fin n)
    (T B C D : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hlive : ∀ i < Q.gates.length,
      Q.output = n+i ∨ ∃ j < Q.gates.length, n+i ∈ (gateAt Q j).inputs)
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hH : ∀ x, gateVal n Q h x = setProduct C D x)
    (hbad : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n Q x (opnd Q h b) = true → x v = true → graphFun G ∅ x = true)
    (hmutual : ∀ x, gateVal n Q g x = true → gateVal n Q h x = true →
      graphFun G ∅ x = true) :
    ∃ Q' : Circuit, IsLeastAO G Q' ∧ Q'.size = Q.size ∧ junk G Q' = {h} := by
  have hgN : g < Q.gates.length := (Finset.mem_filter.mp ((hJ g).mpr (Or.inl rfl))).2.2.1
  have hrootmem : n+r ∈ (gateAt Q g).inputs := by
    rcases hgin with hg | hg <;> rw [hg] <;> simp
  have hrN : r < Q.gates.length := by
    have := hL.1.2.1 g hgN _ hrootmem
    omega
  have hprivate := badRegion_private hL.1 hTF hL.2.1 h4 u T B C D hrN hT hB hrawroot
    (fun k hk => (hJ k).mp hk) hgin hlive hG hH hbad hBD hhfilter
  exact private_projection_exists hL hgh u T B hT hB huB hgood hrawroot hJ hgin hG
    hprivate hmutual

lemma no_least_private_projection {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q)
    {g h r : ℕ} (hgh : g ≠ h) (u : Fin n) (T B : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hprivate : ∀ j, j < Q.gates.length → j ∉ badRegion n Q r T → j ≠ g →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ badRegion n Q r T)
    (hmutual : ∀ x, gateVal n Q g x = true → gateVal n Q h x = true →
      graphFun G ∅ x = true) :
    (∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1) → False := by
  intro hOne
  obtain ⟨E,hE,_,hJE⟩ := private_projection_exists hL hgh u T B hT hB huB hgood
    hrawroot hJ hgin hG hprivate hmutual
  exact hOne E hE (by simp [hJE])

lemma no_least_singleton_flag {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q) (hTF : TopForm G Q)
    (h4 : NoFourCycle G) {g h r : ℕ} (hgh : g ≠ h) (u : Fin n)
    (T B C D : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hlive : ∀ i < Q.gates.length,
      Q.output = n+i ∨ ∃ j < Q.gates.length, n+i ∈ (gateAt Q j).inputs)
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hH : ∀ x, gateVal n Q h x = setProduct C D x)
    (hbad : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n Q x (opnd Q h b) = true → x v = true → graphFun G ∅ x = true)
    (hmutual : ∀ x, gateVal n Q g x = true → gateVal n Q h x = true →
      graphFun G ∅ x = true) :
    (∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1) → False := by
  intro hOne
  obtain ⟨E,hE,_,hJE⟩ := singleton_flag_projection_exists hL hTF h4 hgh u T B C D
    hT hB huB hgood hrawroot hJ hgin hlive hG hH hbad hBD hhfilter hmutual
  exact hOne E hE (by simp [hJE])

lemma independent_operand_raw {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hAO : IsAO2 n Q) (hTF : TopForm G Q)
    {g h w : ℕ} (hgN : g < Q.gates.length) (hgop : (gateAt Q g).op = GateOp.and)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hhnog : ¬ InCone n Q h g) (hw : w ∈ (gateAt Q g).inputs) :
    ∀ k, k < Q.gates.length → OrReaches n Q w k → (gateAt Q k).op = GateOp.or := by
  intro k hk hreach
  have hc : InCone n Q k g := reach_cone n Q g hgN w hw (hAO.2.1 g hgN w hw) k hreach
  rcases gate_op_cases hAO hk with hkAND | hkOR
  · exfalso
    apply hTF k hk g hgN hkAND _ hgop hc
    intro x hx
    by_contra hf
    have hkJ : k ∈ junk G Q := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr hk, hkAND, hk, x, hx, Bool.eq_false_iff.mpr hf⟩
    rcases (hJ k).mp hkJ with he | he
    · have hkg := inCone_lt n Q g k hc
      omega
    · subst k
      exact hhnog hc
  · exact hkOR


lemma singleton_flag_projection_exists_independent {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q) (hTF : TopForm G Q)
    (h4 : NoFourCycle G) {g h r : ℕ} (hgh : g ≠ h) (u : Fin n)
    (T B C D : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hlive : ∀ i < Q.gates.length,
      Q.output = n+i ∨ ∃ j < Q.gates.length, n+i ∈ (gateAt Q j).inputs)
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hH : ∀ x, gateVal n Q h x = setProduct C D x)
    (hbad : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n Q x (opnd Q h b) = true → x v = true → graphFun G ∅ x = true)
    (hind : ¬ InCone n Q g h) :
    ∃ Q' : Circuit, IsLeastAO G Q' ∧ Q'.size = Q.size ∧ junk G Q' = {h} := by
  have hgN : g < Q.gates.length := (Finset.mem_filter.mp ((hJ g).mpr (Or.inl rfl))).2.2.1
  have hrootmem : n+r ∈ (gateAt Q g).inputs := by
    rcases hgin with hg | hg <;> rw [hg] <;> simp
  have hrN : r < Q.gates.length := by
    have := hL.1.2.1 g hgN _ hrootmem
    omega
  have hprivate := badRegion_private hL.1 hTF hL.2.1 h4 u T B C D hrN hT hB hrawroot
    (fun k hk => (hJ k).mp hk) hgin hlive hG hH hbad hBD hhfilter
  exact private_projection_exists_independent hL hgh u T B hT hB huB hgood hrawroot hJ hgin hG
    hprivate hind

lemma no_least_independent_private_projection {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q)
    {g h r : ℕ} (hgh : g ≠ h) (u : Fin n) (T B : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hprivate : ∀ j, j < Q.gates.length → j ∉ badRegion n Q r T → j ≠ g →
      ∀ w ∈ (gateAt Q j).inputs, w < n ∨ w-n ∉ badRegion n Q r T)
    (hind : ¬ InCone n Q g h) :
    (∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1) → False := by
  intro hOne
  obtain ⟨E,hE,_,hJE⟩ := private_projection_exists_independent hL hgh u T B hT hB huB hgood
    hrawroot hJ hgin hG hprivate hind
  exact hOne E hE (by simp [hJE])

lemma no_least_singleton_flag_independent {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {Q : Circuit} (hL : IsLeastAO G Q) (hTF : TopForm G Q)
    (h4 : NoFourCycle G) {g h r : ℕ} (hgh : g ≠ h) (u : Fin n)
    (T B C D : Finset (Fin n))
    (hT : ∀ v, v ∈ T ↔ G.Adj u v) (hB : B = orIn n Q (n+r))
    (huB : u ∉ B) (hgood : 2 ≤ (B ∩ T).card)
    (hrawroot : ∀ k, k < Q.gates.length → OrReaches n Q (n+r) k →
      (gateAt Q k).op = GateOp.or)
    (hJ : ∀ k, k ∈ junk G Q ↔ k = g ∨ k = h)
    (hgin : (gateAt Q g).inputs = [u.val,n+r] ∨
      (gateAt Q g).inputs = [n+r,u.val])
    (hlive : ∀ i < Q.gates.length,
      Q.output = n+i ∨ ∃ j < Q.gates.length, n+i ∈ (gateAt Q j).inputs)
    (hG : ∀ x, gateVal n Q g x = setProduct {u} B x)
    (hH : ∀ x, gateVal n Q h x = setProduct C D x)
    (hbad : ∃ c ∈ C, ∃ d ∈ D, ¬ G.Adj c d)
    (hBD : ∀ b ∈ B, ∀ d ∈ D, ¬ G.Adj b d)
    (hhfilter : ∀ b : Fin 2, ∃ v : Fin n, ∀ x,
      W n Q x (opnd Q h b) = true → x v = true → graphFun G ∅ x = true)
    (hind : ¬ InCone n Q g h) :
    (∀ E : Circuit, IsLeastAO G E → (junk G E).card ≠ 1) → False := by
  intro hOne
  obtain ⟨E,hE,_,hJE⟩ := singleton_flag_projection_exists_independent hL hTF h4 hgh u T B C D
    hT hB huB hgood hrawroot hJ hgin hlive hG hH hbad hBD hhfilter hind
  exact hOne E hE (by simp [hJE])

end SingletonFlagProjection

end PEqualNP.Outside.L_meta_5012
