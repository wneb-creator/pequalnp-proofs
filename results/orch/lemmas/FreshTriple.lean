import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshTriple

def Meets {V : Type*} (S X : Set V) : Prop := ∃ x ∈ X, x ∈ S

def Triple {V : Type*} (A B C X : Set V) : Prop := Meets A X ∧ Meets B X ∧ Meets C X

def InPair {V : Type*} (z u v : V) : Prop := u = z ∨ v = z

def Cross {V : Type*} (A B : Set V) (u v : V) : Prop :=
  (u ∈ A ∧ v ∈ B) ∨ (v ∈ A ∧ u ∈ B)

def LiteralStar {V : Type*} (c : V) (S X : Set V) : Prop := c ∈ X ∧ Meets S X

def Operand {V : Type*} (A B C S : Set V) : Prop := S = A ∨ S = B ∨ S = C

def HasEdge {V : Type*} (G : SimpleGraph V) (X : Set V) : Prop :=
  ∃ a ∈ X, ∃ b ∈ X, G.Adj a b

lemma meets_pair {V : Type*} (A : Set V) (u v : V) : Meets A {u,v} ↔ u ∈ A ∨ v ∈ A := by
  simp [Meets]

lemma hasEdge_pair {V : Type*} {G : SimpleGraph V} {u v : V} :
    HasEdge G {u,v} ↔ G.Adj u v := by
  constructor
  · rintro ⟨a,ha,b,hb,he⟩
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · exact (he.ne rfl).elim
    · exact he
    · exact he.symm
    · exact (he.ne rfl).elim
  · exact fun h => ⟨u,by simp,v,by simp,h⟩

lemma double_cross {V : Type*} (A B C : Set V) (hBC : Disjoint B C) (u v : V) :
    Triple A B C {u,v} ↔ Cross (A ∩ B) C u v ∨ Cross (A ∩ C) B u v := by
  simp only [Triple,meets_pair,Cross,Set.mem_inter_iff]
  have hU : ¬ (u ∈ B ∧ u ∈ C) := fun h => Set.disjoint_left.mp hBC h.1 h.2
  have hV : ¬ (v ∈ B ∧ v ∈ C) := fun h => Set.disjoint_left.mp hBC h.1 h.2
  tauto

lemma disjoint_operands {V : Type*} (G : SimpleGraph V) (A B C : Set V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hs : ∀ u v, Triple A B C {u,v} → G.Adj u v) :
    Disjoint B C ∨ Disjoint A C ∨ Disjoint A B := by
  classical
  by_contra! h
  obtain ⟨z,hzB,hzC⟩ := Set.not_disjoint_iff.mp h.1
  obtain ⟨y,hyA,hyC⟩ := Set.not_disjoint_iff.mp h.2.1
  obtain ⟨x,hxA,hxB⟩ := Set.not_disjoint_iff.mp h.2.2
  have case1 : G.Adj x y := by apply hs; simp [Triple,meets_pair,hxA,hxB,hyC]
  have case2 : G.Adj y z := by apply hs; simp [Triple,meets_pair,hyA,hzB,hzC]
  have case3 : G.Adj z x := by apply hs; simp [Triple,meets_pair,hxA,hxB,hzC]
  exact htri x y z case1 case2 case3

lemma rectangle_center {V : Type*} (G : SimpleGraph V) (A B : Set V)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hab : ∀ a ∈ A, ∀ b ∈ B, G.Adj a b)
    (hne : ∃ u v, Cross A B u v) :
    ∃ c, ∀ u v, Cross A B u v → InPair c u v := by
  classical
  have hAB : ∃ a ∈ A, ∃ b ∈ B, True := by
    obtain ⟨u,v,⟨hu,hv⟩|⟨hv,hu⟩⟩ := hne
    · exact ⟨u,hu,v,hv,trivial⟩
    · exact ⟨v,hv,u,hu,trivial⟩
  obtain ⟨a,ha,b,hb,_⟩ := hAB
  by_cases hA : ∀ x ∈ A, x = a
  · refine ⟨a,?_⟩
    rintro u v (⟨hu,_⟩|⟨hv,_⟩)
    · exact Or.inl (hA u hu)
    · exact Or.inr (hA v hv)
  · push Not at hA
    obtain ⟨x,hx,hxa⟩ := hA
    have hB (y) (hy : y ∈ B) : y = b :=
      (hfour x y a b (hab _ hx _ hy) (hab _ ha _ hy).symm (hab _ ha _ hb)
        (hab _ hx _ hb).symm).resolve_left hxa
    refine ⟨b,?_⟩
    rintro u v (⟨_,hv⟩|⟨_,hu⟩)
    · exact Or.inr (hB v hv)
    · exact Or.inl (hB u hu)

lemma nonstar_overlaps {V : Type*} (G : SimpleGraph V) (A B C : Set V)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hs : ∀ u v, Triple A B C {u,v} → G.Adj u v) (hBC : Disjoint B C)
    (hne : ∃ u v, Triple A B C {u,v})
    (hns : ¬ ∃ c, ∀ u v, Triple A B C {u,v} → InPair c u v) :
    (A ∩ B).Nonempty ∧ (A ∩ C).Nonempty := by
  have hleft : ∀ u ∈ A ∩ B, ∀ v ∈ C, G.Adj u v := by
    intro u hu v hv
    exact hs u v ((double_cross A B C hBC u v).2 (Or.inl (Or.inl ⟨hu,hv⟩)))
  have hright : ∀ u ∈ A ∩ C, ∀ v ∈ B, G.Adj u v := by
    intro u hu v hv
    exact hs u v ((double_cross A B C hBC u v).2 (Or.inr (Or.inl ⟨hu,hv⟩)))
  constructor
  · by_contra h
    have hh (u v) (huv : Triple A B C {u,v}) : Cross (A ∩ C) B u v := by
      rcases (double_cross A B C hBC u v).1 huv with (⟨hu,_⟩|⟨hv,_⟩)|h'
      · exact (h ⟨u,hu⟩).elim
      · exact (h ⟨v,hv⟩).elim
      · exact h'
    obtain ⟨u,v,huv⟩ := hne
    obtain ⟨c,hc⟩ := rectangle_center G _ _ hfour hright ⟨u,v,hh u v huv⟩
    exact hns ⟨c,fun s t hst => hc s t (hh s t hst)⟩
  · by_contra h
    have hh (u v) (huv : Triple A B C {u,v}) : Cross (A ∩ B) C u v := by
      rcases (double_cross A B C hBC u v).1 huv with h'|(⟨hu,_⟩|⟨hv,_⟩)
      · exact h'
      · exact (h ⟨u,hu⟩).elim
      · exact (h ⟨v,hv⟩).elim
    obtain ⟨u,v,huv⟩ := hne
    obtain ⟨c,hc⟩ := rectangle_center G _ _ hfour hleft ⟨u,v,hh u v huv⟩
    exact hns ⟨c,fun s t hst => hc s t (hh s t hst)⟩

lemma oriented_double_star {V : Type*} (G : SimpleGraph V) (A B C : Set V)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hs : ∀ u v, Triple A B C {u,v} → G.Adj u v) (hBC : Disjoint B C)
    {p q : V} (hp : p ∈ A ∩ B) (hq : q ∈ A ∩ C) :
    G.Adj p q ∧ (∀ v ∈ C, G.Adj p v) ∧ (∀ u ∈ B, G.Adj q u) ∧
    (∀ u v, Triple A B C {u,v} ↔
       LiteralStar p C {u,v} ∨ LiteralStar q B {u,v}) := by
  have hB (x) (hx : x ∈ A ∩ B) (y) (hy : y ∈ C) : G.Adj x y :=
    hs x y ((double_cross A B C hBC x y).2 (Or.inl (Or.inl ⟨hx,hy⟩)))
  have hC (x) (hx : x ∈ A ∩ C) (y) (hy : y ∈ B) : G.Adj x y :=
    hs x y ((double_cross A B C hBC x y).2 (Or.inr (Or.inl ⟨hx,hy⟩)))
  refine ⟨hB _ hp _ hq.2,hB _ hp,hC _ hq,?_⟩
  have left (x y) (hx : x ∈ A ∩ B) (hy : y ∈ C) : x = p ∨ y = q :=
    hfour x y p q (hB _ hx _ hy) (hB _ hp _ hy).symm (hB _ hp _ hq.2) (hB _ hx _ hq.2).symm
  have right (x y) (hx : x ∈ A ∩ C) (hy : y ∈ B) : x = q ∨ y = p :=
    hfour x y q p (hC _ hx _ hy) (hC _ hq _ hy).symm (hC _ hq _ hp.2) (hC _ hx _ hp.2).symm
  intro u v
  rw [double_cross A B C hBC]
  constructor
  · rintro ((⟨hu,hv⟩|⟨hv,hu⟩)|(⟨hu,hv⟩|⟨hv,hu⟩))
    · rcases left _ _ hu hv with rfl|rfl
      · exact Or.inl ⟨by simp,(meets_pair C _ _).2 (Or.inr hv)⟩
      · exact Or.inr ⟨by simp,(meets_pair B _ _).2 (Or.inl hu.2)⟩
    · rcases left _ _ hv hu with rfl|rfl
      · exact Or.inl ⟨by simp,(meets_pair C _ _).2 (Or.inl hu)⟩
      · exact Or.inr ⟨by simp,(meets_pair B _ _).2 (Or.inr hv.2)⟩
    · rcases right _ _ hu hv with rfl|rfl
      · exact Or.inr ⟨by simp,(meets_pair B _ _).2 (Or.inr hv)⟩
      · exact Or.inl ⟨by simp,(meets_pair C _ _).2 (Or.inl hu.2)⟩
    · rcases right _ _ hv hu with rfl|rfl
      · exact Or.inr ⟨by simp,(meets_pair B _ _).2 (Or.inl hu)⟩
      · exact Or.inl ⟨by simp,(meets_pair C _ _).2 (Or.inr hv.2)⟩
  · rintro ((⟨hpu,hc⟩)|(⟨hqu,hb⟩))
    · have hnC : p ∉ C := fun h => Set.disjoint_left.mp hBC hp.2 h
      rcases Set.mem_insert_iff.mp hpu with rfl|h
      · exact Or.inl (Or.inl ⟨hp,((meets_pair C _ _).1 hc).resolve_left hnC⟩)
      · have hv := Set.mem_singleton_iff.mp h
        subst v
        exact Or.inl (Or.inr ⟨hp,((meets_pair C _ _).1 hc).resolve_right hnC⟩)
    · have hnB : q ∉ B := fun h => Set.disjoint_left.mp hBC h hq.2
      rcases Set.mem_insert_iff.mp hqu with rfl|h
      · exact Or.inr (Or.inl ⟨hq,((meets_pair B _ _).1 hb).resolve_left hnB⟩)
      · have hv := Set.mem_singleton_iff.mp h
        subst v
        exact Or.inr (Or.inr ⟨hq,((meets_pair B _ _).1 hb).resolve_right hnB⟩)

lemma nonstar_triple_classification {V : Type*} (G : SimpleGraph V) (A B C : Set V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (hs : ∀ X, Triple A B C X → HasEdge G X)
    (hne : ∃ u v, Triple A B C {u,v})
    (hns : ¬ ∃ c, ∀ u v, Triple A B C {u,v} → InPair c u v) :
    ∃ (p q : V) (U L R : Set V), Operand A B C U ∧ Operand A B C L ∧ Operand A B C R ∧
      Disjoint L R ∧ p ∈ U ∩ L ∧ q ∈ U ∩ R ∧ G.Adj p q ∧
      (∀ v ∈ R, G.Adj p v) ∧ (∀ v ∈ L, G.Adj q v) ∧
      (∀ X, LiteralStar p R X ∨ LiteralStar q L X → HasEdge G X) ∧
      (∀ u v, Triple A B C {u,v} ↔ LiteralStar p R {u,v} ∨ LiteralStar q L {u,v}) := by
  have hpairs (u v) (h : Triple A B C {u,v}) : G.Adj u v := hasEdge_pair.mp (hs _ h)
  have horder : ∃ U L R : Set V, Operand A B C U ∧ Operand A B C L ∧ Operand A B C R ∧
      Disjoint L R ∧ ∀ X, Triple A B C X ↔ Triple U L R X := by
    rcases disjoint_operands G A B C htri hpairs with h|h|h
    · exact ⟨A,B,C,Or.inl rfl,Or.inr (Or.inl rfl),Or.inr (Or.inr rfl),h,fun _ => Iff.rfl⟩
    · exact ⟨B,A,C,Or.inr (Or.inl rfl),Or.inl rfl,Or.inr (Or.inr rfl),h,
        fun _ => by unfold Triple; tauto⟩
    · exact ⟨C,A,B,Or.inr (Or.inr rfl),Or.inl rfl,Or.inr (Or.inl rfl),h,
        fun _ => by unfold Triple; tauto⟩
  obtain ⟨U,L,R,hU,hL,hR,hd,heq⟩ := horder
  have hnew (u v) (h : Triple U L R {u,v}) : G.Adj u v := hpairs u v ((heq _).2 h)
  obtain ⟨u,v,hpos⟩ := hne
  have hbad : ¬ ∃ z, ∀ i j, Triple U L R {i,j} → InPair z i j := by
    rintro ⟨z,hz⟩
    exact hns ⟨z,fun i j h => hz i j ((heq _).1 h)⟩
  obtain ⟨⟨p,hp⟩,⟨q,hq⟩⟩ := nonstar_overlaps G U L R hfour hnew hd ⟨u,v,(heq _).1 hpos⟩ hbad
  obtain ⟨hpq,hR',hL',hProfile⟩ := oriented_double_star G U L R hfour hnew hd hp hq
  refine ⟨p,q,U,L,R,hU,hL,hR,hd,hp,hq,hpq,hR',hL',?_,fun i j => (heq _).trans (hProfile i j)⟩
  rintro X (⟨hpX,w,hw,hRw⟩|⟨hqX,w,hw,hLw⟩)
  · exact ⟨p,hpX,w,hw,hR' w hRw⟩
  · exact ⟨q,hqX,w,hw,hL' w hLw⟩

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

end PEqualNP.Outside.L_meta_1031.FreshTriple
