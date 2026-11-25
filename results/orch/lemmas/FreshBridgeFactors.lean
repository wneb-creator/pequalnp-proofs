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
end PEqualNP.Outside.L_meta_1031.FreshBridgeFactors
