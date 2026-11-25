import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_3754.ThreeClause
open PEqualNP.TopForm

def PairSpec {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n)) : Prop :=
  ∀ u v,G.Adj u v ↔ (u∈U ∨ v∈U) ∧ (u∈V ∨ v∈V) ∧ (u∈B ∨ v∈B)

def TripleSpec {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n)) : Prop :=
  ∀ u∈U,∀ v∈V,∀ b∈B,G.Adj u v ∨ G.Adj u b ∨ G.Adj v b

lemma not_subset_witness {α : Type} [DecidableEq α] (A B : Finset α) (h : ¬A⊆B) :
    ∃ x,x∈A ∧ x∉B := by
  classical
  by_contra! hc
  exact h (fun x hx => hc x hx)

lemma not_disjoint_witness {α : Type} [DecidableEq α] (A B : Finset α) (h : ¬Disjoint A B) :
    ∃ x,x∈A ∧ x∈B := by
  classical
  by_contra! hc
  exact h (Finset.disjoint_left.mpr (fun x hx hxb => hc x hx hxb))

lemma some_disjoint_pair {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n))
    (s : Fin n → Bool) (hcolor : ∀ u v,G.Adj u v → s u≠s v)
    (hp : PairSpec G U V B) : Disjoint U V ∨ Disjoint V B ∨ Disjoint B U := by
  classical
  by_cases huv : Disjoint U V
  · exact Or.inl huv
  by_cases hvb : Disjoint V B
  · exact Or.inr (Or.inl hvb)
  by_cases hbu : Disjoint B U
  · exact Or.inr (Or.inr hbu)
  obtain ⟨a,haU,haV⟩ := not_disjoint_witness U V huv
  obtain ⟨b,hbV,hbB⟩ := not_disjoint_witness V B hvb
  obtain ⟨c,hcB,hcU⟩ := not_disjoint_witness B U hbu
  have hab := hcolor a b ((hp a b).mpr ⟨Or.inl haU,Or.inl haV,Or.inr hbB⟩)
  have hbc := hcolor b c ((hp b c).mpr ⟨Or.inr hcU,Or.inl hbV,Or.inl hbB⟩)
  have hca := hcolor c a ((hp c a).mpr ⟨Or.inl hcU,Or.inr haV,Or.inl hcB⟩)
  cases hsa : s a <;> cases hsb : s b <;> cases hsc : s c <;> simp_all

lemma common_eq {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (x y a b : Fin n) (hxy : x≠y)
    (hxa : G.Adj x a) (hya : G.Adj y a) (hxb : G.Adj x b) (hyb : G.Adj y b) : a=b := by
  exact Finset.card_le_one.mp (h4 x y hxy) a (by simp [hxa,hya]) b (by simp [hxb,hyb])

lemma oriented_double_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n)) (h4 : NoFourCycle G)
    (hp : PairSpec G U V B) (ht : TripleSpec G U V B) (hd : Disjoint U V)
    (hUB : ¬U⊆B) (hVB : ¬V⊆B) (hBU : ¬B⊆U) (hBV : ¬B⊆V) :
    ∃ e h,e∈U ∧ h∈V ∧ U∩B={e} ∧ V∩B={h} ∧ B={e,h} ∧ 2≤U.card ∧ 2≤V.card := by
  classical
  obtain ⟨u,hu,hunB⟩ := not_subset_witness U B hUB
  obtain ⟨v,hv,hvnB⟩ := not_subset_witness V B hVB
  have hunV : u∉V := fun hh => Finset.disjoint_left.mp hd hu hh
  have hvnU : v∉U := fun hh => Finset.disjoint_left.mp hd hh hv
  have hsub : B⊆U∪V := by
    intro b hb
    by_contra hbu
    have hbU : b∉U := fun hh => hbu (Finset.mem_union_left V hh)
    have hbV : b∉V := fun hh => hbu (Finset.mem_union_right U hh)
    rcases ht u hu v hv b hb with huv | hub | hvb
    · exact ((hp u v).mp huv).2.2.elim hunB hvnB
    · exact ((hp u b).mp hub).2.1.elim hunV hbV
    · exact ((hp v b).mp hvb).1.elim hvnU hbU
  obtain ⟨e,heB,henV⟩ := not_subset_witness B V hBV
  obtain ⟨h,hhB,hhnU⟩ := not_subset_witness B U hBU
  have heU : e∈U := (Finset.mem_union.mp (hsub heB)).resolve_right henV
  have hhV : h∈V := (Finset.mem_union.mp (hsub hhB)).resolve_left hhnU
  have cross (a b : Fin n) (ha : a∈U) (hb : b∈V) (hB : a∈B ∨ b∈B) : G.Adj a b :=
    (hp a b).mpr ⟨Or.inl ha,Or.inr hb,hB⟩
  have hE : ∀ z,z∈U → z∈B → z=e := by
    intro z hzU hzB
    by_contra hze
    have hhv := common_eq G h4 z e h v hze
      (cross z h hzU hhV (Or.inl hzB)) (cross e h heU hhV (Or.inl heB))
      (cross z v hzU hv (Or.inl hzB)) (cross e v heU hv (Or.inl heB))
    exact hvnB (hhv ▸ hhB)
  have hH : ∀ z,z∈V → z∈B → z=h := by
    intro z hzV hzB
    by_contra hzh
    have heu := common_eq G h4 z h e u hzh
      (cross e z heU hzV (Or.inr hzB)).symm (cross e h heU hhV (Or.inr hhB)).symm
      (cross u z hu hzV (Or.inr hzB)).symm (cross u h hu hhV (Or.inr hhB)).symm
    exact hunB (heu ▸ heB)
  refine ⟨e,h,heU,hhV,?_,?_,?_,?_,?_⟩
  · ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    exact ⟨fun hz => hE z hz.1 hz.2,fun hz => hz.symm ▸ ⟨heU,heB⟩⟩
  · ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    exact ⟨fun hz => hH z hz.1 hz.2,fun hz => hz.symm ▸ ⟨hhV,hhB⟩⟩
  · ext z
    constructor
    · intro hz
      rcases Finset.mem_union.mp (hsub hz) with hzU | hzV
      · simp [hE z hzU hz]
      · simp [hH z hzV hz]
    · intro hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      exact hz.elim (fun hz => hz.symm ▸ heB) (fun hz => hz.symm ▸ hhB)
  · by_contra hn
    have hc : U.card≤1 := by omega
    have heu := Finset.card_le_one.mp hc e heU u hu
    exact hunB (heu ▸ heB)
  · by_contra hn
    have hc : V.card≤1 := by omega
    have hhv := Finset.card_le_one.mp hc h hhV v hv
    exact hvnB (hhv ▸ hhB)


open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def orQ {n : ℕ} (Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ u∈Q,x u=true)

lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x=true ↔ ∃ u v : Fin n,G.Adj u v ∧ x u=true ∧ x v=true := by
  unfold graphFun
  simp

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v)=true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a,b,hab,ha,hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u,v,huv,by simp [pairInput],by simp [pairInput]⟩

lemma orQ_pair {n : ℕ} (Q : Finset (Fin n)) (u v : Fin n) :
    orQ Q (pairInput u v)=true ↔ u∈Q ∨ v∈Q := by
  simp only [orQ,pairInput,decide_eq_true_eq]
  constructor
  · rintro ⟨w,hw,hwu | hwv⟩
    · exact Or.inl (hwu ▸ hw)
    · exact Or.inr (hwv ▸ hw)
  · rintro (hu | hv)
    · exact ⟨u,hu,Or.inl rfl⟩
    · exact ⟨v,hv,Or.inr rfl⟩

lemma product_specs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n))
    (hf : ∀ x : Fin n → Bool,graphFun G ∅ x=(orQ U x && orQ V x && orQ B x)) :
    PairSpec G U V B ∧ TripleSpec G U V B := by
  constructor
  · intro u v
    rw [←graphFun_pair_iff u v,hf]
    simp only [Bool.and_eq_true,orQ_pair,and_assoc]
  · intro u hu v hv b hb
    let x : Fin n → Bool := fun w => decide (w=u ∨ w=v ∨ w=b)
    have hU : orQ U x=true := decide_eq_true ⟨u,hu,by simp [x]⟩
    have hV : orQ V x=true := decide_eq_true ⟨v,hv,by simp [x]⟩
    have hB : orQ B x=true := decide_eq_true ⟨b,hb,by simp [x]⟩
    have hF : graphFun G ∅ x=true := by rw [hf,hU,hV,hB];rfl
    obtain ⟨a,c,hac,ha,hc⟩ := (graphFun_iff x).mp hF
    simp only [x,decide_eq_true_eq] at ha hc
    rcases ha with rfl | rfl | rfl <;> rcases hc with rfl | rfl | rfl
    all_goals first
      | exact (G.loopless.irrefl _ hac).elim
      | exact Or.inl hac
      | exact Or.inl hac.symm
      | exact Or.inr (Or.inl hac)
      | exact Or.inr (Or.inl hac.symm)
      | exact Or.inr (Or.inr hac)
      | exact Or.inr (Or.inr hac.symm)

def DoubleStar {n : ℕ} (U V B : Finset (Fin n)) : Prop :=
  Disjoint U V ∧ ∃ e h,e∈U ∧ h∈V ∧ U∩B={e} ∧ V∩B={h} ∧ B={e,h} ∧ 2≤U.card ∧ 2≤V.card

lemma cyclic_specs {n : ℕ} (G : SimpleGraph (Fin n)) (U V B : Finset (Fin n))
    (hp : PairSpec G U V B) (ht : TripleSpec G U V B) :
    PairSpec G V B U ∧ TripleSpec G V B U := by
  constructor
  · intro u v
    constructor
    · intro h
      have h := (hp u v).mp h
      exact ⟨h.2.1,h.2.2,h.1⟩
    · rintro ⟨hV,hB,hU⟩
      exact (hp u v).mpr ⟨hU,hV,hB⟩
  · intro v hv b hb u hu
    rcases ht u hu v hv b hb with huv | hub | hvb
    · exact Or.inr (Or.inl huv.symm)
    · exact Or.inr (Or.inr hub.symm)
    · exact Or.inl hvb

lemma irredundant_product_double_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (U V B : Finset (Fin n)) (s : Fin n → Bool)
    (hcolor : ∀ u v,G.Adj u v → s u≠s v) (h4 : NoFourCycle G)
    (hf : ∀ x : Fin n → Bool,graphFun G ∅ x=(orQ U x && orQ V x && orQ B x))
    (hUV : ¬U⊆V) (hVU : ¬V⊆U) (hUB : ¬U⊆B) (hBU : ¬B⊆U)
    (hVB : ¬V⊆B) (hBV : ¬B⊆V) :
    DoubleStar U V B ∨ DoubleStar V B U ∨ DoubleStar B U V := by
  obtain ⟨hp,ht⟩ := product_specs G U V B hf
  rcases some_disjoint_pair G U V B s hcolor hp with hd | hd | hd
  · exact Or.inl ⟨hd,oriented_double_star G U V B h4 hp ht hd hUB hVB hBU hBV⟩
  · obtain ⟨hp',ht'⟩ := cyclic_specs G U V B hp ht
    exact Or.inr (Or.inl ⟨hd,oriented_double_star G V B U h4 hp' ht' hd hVU hBU hUV hUB⟩)
  · obtain ⟨hp',ht'⟩ := cyclic_specs G U V B hp ht
    obtain ⟨hp'',ht''⟩ := cyclic_specs G V B U hp' ht'
    exact Or.inr (Or.inr ⟨hd,oriented_double_star G B U V h4 hp'' ht'' hd hBV hUV hVB hVU⟩)

end PEqualNP.Outside.L_meta_3754.ThreeClause
