import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshBridgeFactors

def Meets {V : Type*} (S X : Set V) : Prop := ∃ x ∈ X, x ∈ S

def Triple {V : Type*} (A B C X : Set V) : Prop := Meets A X ∧ Meets B X ∧ Meets C X

def InPair {V : Type*} (z u v : V) : Prop := u = z ∨ v = z

def Cross {V : Type*} (A B : Set V) (u v : V) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B)

def LiteralStar {V : Type*} (c : V) (S X : Set V) : Prop := c ∈ X ∧ Meets S X

def Operand {V : Type*} (A B C S : Set V) : Prop := S = A ∨ S = B ∨ S = C

def HasEdge {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, G.Adj a b

lemma extra_vertex_choice {V : Type*} (G : SimpleGraph V) (U L R : Set V)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hs : ∀ X, Triple U L R X → HasEdge G X)
    {p q : V} (hpq : G.Adj p q) (hL : ∀ v ∈ L, G.Adj q v) (hR : ∀ v ∈ R, G.Adj p v)
    {x l r : V} (hx : x ∈ U) (hl : l ∈ L) (hr : r ∈ R) (hlp : l ≠ p) (hrq : r ≠ q) :
    G.Adj x l ∨ G.Adj x r := by
  have hnlr : ¬ G.Adj l r := by
    intro h
    exact (hfour l r p q h (hR r hr).symm hpq (hL l hl)).elim hlp hrq
  have hh : Triple U L R ({x,l,r} : Set V) :=
    ⟨⟨x,by simp,hx⟩,⟨l,by simp,hl⟩,⟨r,by simp,hr⟩⟩
  obtain ⟨a,ha,b,hb,he⟩ := hs _ hh
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl|rfl|rfl <;> rcases hb with h|h|h <;> subst b
  all_goals first | exact (he.ne rfl).elim | exact Or.inl he | exact Or.inr he |
    exact Or.inl he.symm | exact Or.inr he.symm | exact (hnlr he).elim | exact (hnlr he.symm).elim

lemma extra_vertex_nonadjacent {V : Type*} (G : SimpleGraph V) (U L R : Set V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hs : ∀ X, Triple U L R X → HasEdge G X)
    {p q : V} (hpq : G.Adj p q) (hL : ∀ v ∈ L, G.Adj q v) (hR : ∀ v ∈ R, G.Adj p v)
    {x l r : V} (hx : x ∈ U) (hl : l ∈ L) (hr : r ∈ R)
    (hlp : l ≠ p) (hrq : r ≠ q) (hxp : x ≠ p) (hxq : x ≠ q) :
    ¬ G.Adj x p ∧ ¬ G.Adj x q := by
  rcases extra_vertex_choice G U L R hfour hs hpq hL hR hx hl hr hlp hrq with h|h
  · exact ⟨fun hxp' => (hfour x l q p h (hL l hl).symm hpq.symm hxp'.symm).elim hxq hlp,
      htri q l x (hL l hl) h.symm⟩
  · exact ⟨htri p r x (hR r hr) h.symm,
      fun hxq' => (hfour x r p q h (hR r hr).symm hpq hxq'.symm).elim hxp hrq⟩


def NoTri {V : Type*} (G : SimpleGraph V) := ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a

def NoSq {V : Type*} (G : SimpleGraph V) :=
  ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d

structure Branch {V : Type*} (G : SimpleGraph V) (U : Set V) where
  p : V
  q : V
  left : Set V
  right : Set V
  pU : p ∈ U
  qU : q ∈ U
  pL : p ∈ left
  qR : q ∈ right
  edge : G.Adj p q
  nearL : ∀ x ∈ left, G.Adj q x
  nearR : ∀ x ∈ right, G.Adj p x
  sound : ∀ X, Triple U left right X → HasEdge G X
  pairProfile : ∀ u v, Triple U left right {u,v} ↔
    LiteralStar p right {u,v} ∨ LiteralStar q left {u,v}
  noCenter : ¬ ∃ z, ∀ u v, Triple U left right {u,v} → InPair z u v

namespace Branch
variable {V : Type*} {G : SimpleGraph V} {U : Set V} (B : Branch G U)

lemma mem_pair_to_inPair {z u v : V} (h : z ∈ ({u,v} : Set V)) : InPair z u v := by
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  exact h.imp Eq.symm Eq.symm

lemma left_witness : ∃ l ∈ B.left, l ≠ B.p := by
  classical
  by_contra! h
  apply B.noCenter
  refine ⟨B.p,?_⟩
  intro u v huv
  rcases (B.pairProfile u v).1 huv with ⟨hp,_⟩|⟨_,w,hw,hL⟩
  · exact mem_pair_to_inPair hp
  · rw [h w hL] at hw
    exact mem_pair_to_inPair hw

lemma right_witness : ∃ r ∈ B.right, r ≠ B.q := by
  classical
  by_contra! h
  apply B.noCenter
  refine ⟨B.q,?_⟩
  intro u v huv
  rcases (B.pairProfile u v).1 huv with ⟨_,w,hw,hR⟩|⟨hq,_⟩
  · rw [h w hR] at hw
    exact mem_pair_to_inPair hw
  · exact mem_pair_to_inPair hq

lemma isolate (h3 : NoTri G) (h4 : NoSq G) {x : V} (hx : x ∈ U) (hxp : x ≠ B.p) (hxq : x ≠ B.q) :
    ¬ G.Adj x B.p ∧ ¬ G.Adj x B.q := by
  obtain ⟨l,hl,hlp⟩ := B.left_witness
  obtain ⟨r,hr,hrq⟩ := B.right_witness
  exact extra_vertex_nonadjacent G U B.left B.right h3 h4 B.sound B.edge B.nearL B.nearR
    hx hl hr hlp hrq hxp hxq

lemma induced_edge (h3 : NoTri G) (h4 : NoSq G) {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (he : G.Adj a b) :
    ({B.p,B.q} : Set V) = {a,b} ∨ Disjoint ({B.p,B.q} : Set V) {a,b} := by
  classical
  have det {x y : V} (hx : x ∈ U) (hxy : G.Adj x y) (hy : y = B.p ∨ y = B.q) :
      x = B.p ∨ x = B.q := by
    by_contra! h
    rcases hy with rfl | rfl
    · exact (B.isolate h3 h4 hx h.1 h.2).1 hxy
    · exact (B.isolate h3 h4 hx h.1 h.2).2 hxy
  by_cases h : Disjoint ({B.p,B.q} : Set V) {a,b}
  · exact Or.inr h
  left
  obtain ⟨x,hx,hy⟩ := Set.not_disjoint_iff.mp h
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
  rcases hy with rfl|rfl
  · have hb' := det hb he.symm hx
    rcases hx with h|h <;> rcases hb' with h'|h'
    · exact (he.ne (h.trans h'.symm)).elim
    · simp [h,h']
    · simp [h,h',Set.pair_comm]
    · exact (he.ne (h.trans h'.symm)).elim
  · have ha' := det ha he hx
    rcases hx with h|h <;> rcases ha' with h'|h'
    · exact (he.ne (h'.trans h.symm)).elim
    · simp [h,h',Set.pair_comm]
    · simp [h,h']
    · exact (he.ne (h'.trans h.symm)).elim

lemma split_bridge (h3 : NoTri G) (h4 : NoSq G) {a b l r : V}
    (ha : a ∈ U) (hb : b ∈ U) (he : G.Adj a b)
    (hl : l ∈ B.left) (hlp : l ≠ B.p) (hr : r ∈ B.right) (hrq : r ≠ B.q) :
    (G.Adj a l ∧ G.Adj b r) ∨ (G.Adj a r ∧ G.Adj b l) := by
  have choose {x : V} (hx : x ∈ U) := extra_vertex_choice G U B.left B.right h4 B.sound
    B.edge B.nearL B.nearR hx hl hr hlp hrq
  rcases choose ha with al|ar <;> rcases choose hb with bl|br
  · exact (h3 a b l he bl al.symm).elim
  · exact Or.inl ⟨al,br⟩
  · exact Or.inr ⟨ar,bl⟩
  · exact (h3 a b r he br ar.symm).elim

lemma left_unique (h3 : NoTri G) (h4 : NoSq G) {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (he : G.Adj a b) (haq : a ≠ B.q) (hbq : b ≠ B.q)
    {l l' : V} (hl : l ∈ B.left) (hlp : l ≠ B.p) (hl' : l' ∈ B.left) (hlp' : l' ≠ B.p) : l=l' := by
  obtain ⟨r,hr,hrq⟩ := B.right_witness
  have one := B.split_bridge h3 h4 ha hb he hl hlp hr hrq
  have two := B.split_bridge h3 h4 ha hb he hl' hlp' hr hrq
  rcases one with ⟨al,br⟩|⟨ar,bl⟩ <;> rcases two with ⟨al',br'⟩|⟨ar',bl'⟩
  · exact (h4 l a l' B.q al.symm al' (B.nearL _ hl').symm (B.nearL _ hl)).resolve_right haq
  · exact (h3 a b r he br ar'.symm).elim
  · exact (h3 a b r he br' ar.symm).elim
  · exact (h4 l b l' B.q bl.symm bl' (B.nearL _ hl').symm (B.nearL _ hl)).resolve_right hbq

lemma right_unique (h3 : NoTri G) (h4 : NoSq G) {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (he : G.Adj a b) (hap : a ≠ B.p) (hbp : b ≠ B.p)
    {r r' : V} (hr : r ∈ B.right) (hrq : r ≠ B.q) (hr' : r' ∈ B.right) (hrq' : r' ≠ B.q) : r=r' := by
  obtain ⟨l,hl,hlp⟩ := B.left_witness
  have one := B.split_bridge h3 h4 ha hb he hl hlp hr hrq
  have two := B.split_bridge h3 h4 ha hb he hl hlp hr' hrq'
  rcases one with ⟨al,br⟩|⟨ar,bl⟩ <;> rcases two with ⟨al',br'⟩|⟨ar',bl'⟩
  · exact (h4 r b r' B.p br.symm br' (B.nearR _ hr').symm (B.nearR _ hr)).resolve_right hbp
  · exact (h3 a b l he bl' al.symm).elim
  · exact (h3 a b l he bl al'.symm).elim
  · exact (h4 r a r' B.p ar.symm ar' (B.nearR _ hr').symm (B.nearR _ hr)).resolve_right hap

lemma exact_operands_of_second_bridge (h3 : NoTri G) (h4 : NoSq G) {a b : V}
    (ha : a ∈ U) (hb : b ∈ U) (he : G.Adj a b)
    (hd : ({B.p,B.q} : Set V) ≠ {a,b}) :
    ∃ l r, l ≠ B.p ∧ r ≠ B.q ∧ B.left = {B.p,l} ∧ B.right = {B.q,r} := by
  have h := (B.induced_edge h3 h4 ha hb he).resolve_left hd
  have sep {x y : V} (hx : x ∈ ({a,b} : Set V)) (hy : y ∈ ({B.p,B.q} : Set V)) : x ≠ y := by
    rintro rfl
    exact Set.disjoint_left.mp h hy hx
  obtain ⟨l,hl,hlp⟩ := B.left_witness
  obtain ⟨r,hr,hrq⟩ := B.right_witness
  refine ⟨l,r,hlp,hrq,?_,?_⟩
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      by_cases heq : x=B.p
      · exact Or.inl heq
      · exact Or.inr (B.left_unique h3 h4 ha hb he (sep (by simp) (by simp))
          (sep (by simp) (by simp)) hx heq hl hlp)
    · rintro (rfl|rfl)
      · exact B.pL
      · exact hl
  · ext x
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    constructor
    · intro hx
      by_cases heq : x=B.q
      · exact Or.inl heq
      · exact Or.inr (B.right_unique h3 h4 ha hb he (sep (by simp) (by simp))
          (sep (by simp) (by simp)) hx heq hr hrq)
    · rintro (rfl|rfl)
      · exact B.qR
      · exact hr

end Branch
lemma common_pair_eq {V : Type*} {G : SimpleGraph V} (h4 : NoSq G) {x y a b : V}
    (hab : a ≠ b) (hxa : G.Adj x a) (hxb : G.Adj x b)
    (hya : G.Adj y a) (hyb : G.Adj y b) : x = y :=
  (h4 x a y b hxa hya.symm hyb hxb.symm).resolve_right hab

lemma three_hits {V : Type*} {G : SimpleGraph V} (h4 : NoSq G) {p q z a b c : V}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : G.Adj z a) (hzb : G.Adj z b) (hzc : G.Adj z c)
    (ha : G.Adj p a ∨ G.Adj q a) (hb : G.Adj p b ∨ G.Adj q b)
    (hc : G.Adj p c ∨ G.Adj q c) : z = p ∨ z = q := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact Or.inl (common_pair_eq h4 hab hza hzb ha hb)
  · rcases hc with hc | hc
    · exact Or.inl (common_pair_eq h4 hac hza hzc ha hc)
    · exact Or.inr (common_pair_eq h4 hbc hzb hzc hb hc)
  · rcases hc with hc | hc
    · exact Or.inl (common_pair_eq h4 hbc hzb hzc hb hc)
    · exact Or.inr (common_pair_eq h4 hac hza hzc ha hc)
  · exact Or.inr (common_pair_eq h4 hab hza hzb ha hb)

def Joins {V ι : Type*} (G : SimpleGraph V) (L R : ι → V) (x : V) : Prop :=
  ∀ i, G.Adj x (L i) ∨ G.Adj x (R i)

def Opposed {V ι : Type*} (G : SimpleGraph V) (L R : ι → V) (x y : V) : Prop :=
  ∀ i, (G.Adj x (L i) ∧ G.Adj y (R i)) ∨ (G.Adj x (R i) ∧ G.Adj y (L i))

def DisjointEdges {V ι : Type*} (L R : ι → V) : Prop :=
  Pairwise fun i j => Disjoint ({L i, R i} : Set V) {L j, R j}

lemma opposed_symm {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {x y : V}
    (h : Opposed G L R x y) : Opposed G L R y x := by
  intro i
  rcases h i with ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact Or.inr ⟨h2,h1⟩
  · exact Or.inl ⟨h2,h1⟩

lemma endpoint_ne {V ι : Type*} {L R : ι → V} (hd : DisjointEdges L R)
    {i j : ι} (hij : i ≠ j) {a b : V}
    (ha : a ∈ ({L i,R i} : Set V)) (hb : b ∈ ({L j,R j} : Set V)) : a ≠ b := by
  rintro rfl
  exact Set.disjoint_left.mp (hd hij) ha hb

lemma endpoint_hit {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {x : V}
    (h : Joins G L R x) (i : ι) : ∃ a ∈ ({L i,R i} : Set V), G.Adj x a := by
  rcases h i with h | h
  · exact ⟨L i,by simp,h⟩
  · exact ⟨R i,by simp,h⟩

lemma opposed_dominate {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {p q : V}
    (h : Opposed G L R p q) {i : ι} {a : V} (ha : a ∈ ({L i,R i} : Set V)) :
    G.Adj p a ∨ G.Adj q a := by
  rcases Set.mem_insert_iff.mp ha with he | he
  · subst a
    rcases h i with hh | hh
    · exact Or.inl hh.1
    · exact Or.inr hh.2
  · obtain rfl := Set.mem_singleton_iff.mp he
    rcases h i with hh | hh
    · exact Or.inr hh.2
    · exact Or.inl hh.1

lemma three_bridges_unique {V ι : Type*} {G : SimpleGraph V} (h4 : NoSq G)
    {L R : ι → V} (hd : DisjointEdges L R) {i j k : ι} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) {p q z : V} (hpq : Opposed G L R p q)
    (hz : Joins G L R z) : z=p ∨ z=q := by
  obtain ⟨a,hai,hza⟩ := endpoint_hit hz i
  obtain ⟨b,hbj,hzb⟩ := endpoint_hit hz j
  obtain ⟨c,hck,hzc⟩ := endpoint_hit hz k
  exact three_hits h4 (endpoint_ne hd hij hai hbj) (endpoint_ne hd hik hai hck)
    (endpoint_ne hd hjk hbj hck) hza hzb hzc (opposed_dominate hpq hai)
    (opposed_dominate hpq hbj) (opposed_dominate hpq hck)


lemma branches_opposed {V ι : Type*} {G : SimpleGraph V} {U : Set V}
    (h3 : NoTri G) (h4 : NoSq G) (F : ι → Branch G U) (B : Branch G U)
    {l r : V} (hl : l ∈ B.left) (hlp : l ≠ B.p) (hr : r ∈ B.right) (hrq : r ≠ B.q) :
    Opposed G (fun i => (F i).p) (fun i => (F i).q) l r := by
  intro i
  rcases B.split_bridge h3 h4 (F i).pU (F i).qU (F i).edge hl hlp hr hrq with ⟨u,v⟩|⟨u,v⟩
  · exact Or.inl ⟨u.symm,v.symm⟩
  · exact Or.inr ⟨v.symm,u.symm⟩

lemma joins_left {V ι : Type*} {G : SimpleGraph V} {L R : ι → V} {x y : V}
    (h : Opposed G L R x y) : Joins G L R x := by
  intro i
  exact (h i).imp And.left And.left

lemma three_bridge_family {V ι : Type*} {G : SimpleGraph V} {U : Set V}
    (h3 : NoTri G) (h4 : NoSq G) (F : ι → Branch G U)
    (hIJ : Function.Injective fun i => ({(F i).p,(F i).q} : Set V))
    {i j k : ι} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∃ l r : V, l ≠ r ∧ ∀ B : Branch G U,
      (B.left = {B.p,l} ∧ B.right = {B.q,r}) ∨
      (B.left = {B.p,r} ∧ B.right = {B.q,l}) := by
  classical
  let P := fun t => (F t).p
  let Q := fun t => (F t).q
  have hDI : DisjointEdges P Q := by
    intro s t hst
    exact ((F s).induced_edge h3 h4 (F t).pU (F t).qU (F t).edge).resolve_left (fun h => hst (hIJ h))
  obtain ⟨l,hl,hlp⟩ := (F i).left_witness
  obtain ⟨r,hr,hrq⟩ := (F i).right_witness
  have ref : Opposed G P Q l r := branches_opposed h3 h4 F (F i) hl hlp hr hrq
  have distinct (B : Branch G U) {x y : V} (hx : x ∈ B.left) (hy : y ∈ B.right) : x ≠ y := by
    rintro rfl
    exact h3 B.p B.q x B.edge (B.nearL x hx) (B.nearR x hy).symm
  refine ⟨l,r,distinct (F i) hl hr,?_⟩
  intro B
  have other : ∃ t : ι, ({B.p,B.q} : Set V) ≠ {(F t).p,(F t).q} := by
    by_cases h : ({B.p,B.q} : Set V) = {(F i).p,(F i).q}
    · exact ⟨j,fun hh => hij (hIJ (h.symm.trans hh))⟩
    · exact ⟨i,h⟩
  obtain ⟨t,ht⟩ := other
  obtain ⟨x,y,hxp,hyq,hL,hR⟩ := B.exact_operands_of_second_bridge h3 h4 (F t).pU (F t).qU (F t).edge ht
  have hx : x ∈ B.left := by simp [hL]
  have hy : y ∈ B.right := by simp [hR]
  have hxy : x ≠ y := distinct B hx hy
  have opp : Opposed G P Q x y := branches_opposed h3 h4 F B hx hxp hy hyq
  have dx := three_bridges_unique h4 hDI hij hik hjk ref (joins_left opp)
  have dy := three_bridges_unique h4 hDI hij hik hjk ref (joins_left (opposed_symm opp))
  rcases dx with hh|hh <;> rcases dy with hh'|hh'
  · exact (hxy (hh.trans hh'.symm)).elim
  · exact Or.inl ⟨hh ▸ hL,hh' ▸ hR⟩
  · exact Or.inr ⟨hh ▸ hL,hh' ▸ hR⟩
  · exact (hxy (hh.trans hh'.symm)).elim

end PEqualNP.Outside.L_meta_1031.FreshBridgeFactors
