import UpstreamGraph

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

abbrev EdgeIdx := Fin 19

abbrev Slot := ℕ × Bool

def endpoint (s : Bool) (e : EdgeIdx) : V :=
  let ab := edges.getD e.val (0,0)
  Fin.ofNat 14 (if s then ab.2 else ab.1)

def flip (s : Bool) (e : Slot) := if s then sem_bar e else e

theorem flip_inj (s : Bool) : Function.Injective (flip s) := by
  intro a b
  cases s with
  | false => exact id
  | true =>
    intro eq
    have h := congrArg sem_bar eq
    simpa only [flip,if_true,sem_bar_bar] using h

def AtSlots (D : Dag) (P : EdgeIdx → Slot) :=
  ∀ s e, flip s (P e) ∈ sem_W 14 D (endpoint s e)

theorem get_slots {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) : ∃ P, AtSlots D P := by
  have adjE : ∀ e : EdgeIdx, adj (endpoint false e) (endpoint true e) := by decide +kernel
  have both (e : EdgeIdx) : ∃ p : Slot,
      p∈sem_W 14 D (endpoint false e) ∧ sem_bar p∈sem_W 14 D (endpoint true e) := by
    obtain ⟨p,hl,hr,_⟩ := sem_edge_slots graph_ok h.1 hc (adjE e)
    exact ⟨p,hl,hr⟩
  choose P hp using both
  exact ⟨P,fun s e => by cases s; exact (hp e).1; exact (hp e).2⟩

theorem at_most_two {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (tight : Bplus 14 D ≤ (eligSet 14 D).card) : ∀ x, (sem_W 14 D x).card≤2 := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have zero : residualUnits 14 D b = ∅ := by
    have := card_residual h.1 b hb
    exact Finset.card_eq_zero.mp (by omega)
  intro x
  have count := sem_code_count graph_ok h hc b hb x
  have one := Finset.card_le_card (Finset.inter_subset_left : ({x} : Finset V) ∩ eligSet 14 D ⊆ {x})
  rw [zero] at count
  simp only [Finset.filter_empty,Finset.card_empty,Finset.card_singleton] at count one
  omega

theorem all_equal {D : Dag} {P} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hp : AtSlots D P)
    (s : Bool) (a b : EdgeIdx) (same : endpoint s a=endpoint s b)
    (hi : endpoint s a ∈ ineligSet 14 D) : P a=P b := by
  obtain ⟨e,_,_,_,_,_,hw,_⟩ := sem_inelig_consumer graph_ok h hc hi
  change sem_W 14 D (endpoint s a)={e} at hw
  have ha := hp s a
  have hb := hp s b
  rw [←same] at hb
  exact flip_inj s ((Finset.mem_singleton.mp (hw ▸ ha)).trans (Finset.mem_singleton.mp (hw ▸ hb)).symm)

theorem pure_slot {D : Dag} {P} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hp : AtSlots D P)
    (s : Bool) (a b : EdgeIdx) (diff : endpoint s a≠endpoint s b)
    (hi : endpoint s a∈ineligSet 14 D) : P a≠P b := by
  intro eq
  have ha := (sem_mem_W.mp (hp s a)).2.1
  have hb := (sem_mem_W.mp (hp s b)).2.1
  rw [←eq] at hb
  rw [sem_inelig_pure graph_ok h.1 hc hi ha,Finset.mem_singleton] at hb
  exact diff hb.symm

theorem couple {D : Dag} {P} (hp : AtSlots D P) (lim : ∀ x, (sem_W 14 D x).card≤2)
    (s : Bool) (a b c : EdgeIdx) (same : endpoint s a=endpoint s b ∧ endpoint s a=endpoint s c) :
    P a=P b ∨ P b=P c ∨ P a=P c := by
  by_contra! ne
  have hb := hp s b
  have hc := hp s c
  rw [←same.1] at hb
  rw [←same.2] at hc
  have card := Finset.two_lt_card.mpr ⟨_,hp s a,_,hb,_,hc,fun e => ne.1 (flip_inj s e),
    fun e => ne.2.2 (flip_inj s e),fun e => ne.2.1 (flip_inj s e)⟩
  exact (Nat.not_lt_of_ge (lim _)) card

theorem exposure {D : Dag} {P} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hp : AtSlots D P)
    (lim : ∀ x, (sem_W 14 D x).card≤2) (s : Bool) (a b i j : EdgeIdx) (q : V)
    (geom : endpoint s a=endpoint s b ∧ ¬adj (endpoint s i) (endpoint s j) ∧
      adj (endpoint s a) q ∧ ¬adj q (endpoint s i) ∧ ¬adj q (endpoint s j)) :
    P a=P b ∨ P a≠P i ∨ P b≠P j := by
  by_contra! bad
  obtain ⟨sw,na,hq,ni,nj⟩ := geom
  obtain ⟨e,he,no1,no2⟩ := sem_cover_free graph_ok h.1 hc na hq ni nj
  have mb := hp s b
  rw [←sw] at mb
  have yi := (sem_mem_W.mp (hp s i)).2.1
  have yj := (sem_mem_W.mp (hp s j)).2.1
  rw [←bad.2.1] at yi
  rw [←bad.2.2] at yj
  have ne1 : flip s (P a)≠e := fun eq => no1 (eq ▸ yi)
  have ne2 : flip s (P b)≠e := fun eq => no2 (eq ▸ yj)
  have card := Finset.two_lt_card.mpr ⟨_,hp s a,_,mb,e,he,fun eq => bad.1 (flip_inj s eq),ne1,ne2⟩
  exact (Nat.not_lt_of_ge (lim _)) card

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

set_option maxHeartbeats 0 in
theorem exact_position {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (P : Finset V) (ind : independent P) (i x : V) (hi : i∈ineligSet 14 D) (xin : x∈P) (ix : adj i x) :
    ∃ e ∈ sem_W 14 D x, ∀ a∈P, a∈supp 14 D (src D e) ↔ adj i a := by
  obtain ⟨j,s,hj,ht,ch,ex⟩ := sem_exact_nbhd graph_ok h.1 hc P ind (sem_noempty_chain_out graph_ok h hc z hi)
  refine ⟨(j,s),sem_mem_W.mpr ⟨hj,(ex _ xin).2 ix,?_⟩,ex⟩
  intro hx
  have pure := sem_dom_pure graph_ok h.1 hc i _ (sem_chain_dom h.1 ch)
  have eq := Finset.mem_singleton.mp (pure (sem_supp_and_sub h.1 hj ht (!s) hx))
  exact graph_ok.2.1 i (eq ▸ ix)

def MissingTwo (D : Dag) (x c : V) : Prop :=
  ∃ e∈sem_W 14 D x, ∃ f∈sem_W 14 D x, e≠f ∧ c∉supp 14 D (src D e) ∧ c∉supp 14 D (src D f)

set_option maxHeartbeats 0 in
theorem two_exact {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (P : Finset V) (ind : independent P) (i j x c y : V) (hi : i∈ineligSet 14 D) (hj : j∈ineligSet 14 D)
    (g : x∈P ∧ c∈P ∧ y∈P ∧ adj i x ∧ adj j x ∧ ¬adj i c ∧ ¬adj j c ∧ adj i y ∧ ¬adj j y) : MissingTwo D x c := by
  rcases g with ⟨xp,cp,yp,ix,jx,ic,jc,iy,jy⟩
  obtain ⟨e,he,E⟩ := exact_position h hc z P ind i x hi xp ix
  obtain ⟨f,hf,F⟩ := exact_position h hc z P ind j x hj xp jx
  refine ⟨e,he,f,hf,?_,fun q => ic ((E _ cp).1 q),fun q => jc ((F _ cp).1 q)⟩
  rintro rfl; exact jy ((F _ yp).1 ((E _ yp).2 iy))

set_option maxHeartbeats 0 in
theorem exposed_exact {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0)
    (P A : Finset V) (ind : independent P) (indA : independent A) (i x c : V) (hi : i∈ineligSet 14 D)
    (g : x∈P ∧ c∈P ∧ c∈A ∧ adj i x ∧ ¬adj i c ∧ (∃ a∈A, adj x a) ∧ ∃ y∈P, y∈A ∧ adj i y) : MissingTwo D x c := by
  rcases g with ⟨xp,cp,ca,ix,ic,xa,y,yp,ya,iy⟩
  obtain ⟨e,he,E⟩ := exact_position h hc z P ind i x hi xp ix
  obtain ⟨j,s,js,_,xs,no,free⟩ := sem_exposure graph_ok h.1 hc A indA x xa
  refine ⟨e,he,(j,s),sem_mem_W.mpr ⟨js,xs,no⟩,?_,fun q => ic ((E _ cp).1 q),fun q => Finset.disjoint_left.mp free q ca⟩
  rintro rfl; exact Finset.disjoint_left.mp free ((E _ yp).2 iy) ya

def code {k : Nat} {D : Dag} {b : V → Nat} (f : Fin k ≃ ↥(residualUnits 14 D b)) (x : V) : Finset (Fin k) :=
  Finset.univ.filter (fun t => x∈supp 14 D (f t).val.1)

set_option maxHeartbeats 0 in
theorem code_diff {k : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (b : V → Nat) (hb : PureBranch 14 D b) (f : Fin k ≃ ↥(residualUnits 14 D b)) (x c : V)
    (ne : x≠c) (elig : x∈eligSet 14 D) (miss : MissingTwo D x c)
    (together : ∃ w, x∈supp 14 D w ∧ c∈supp 14 D w) : ¬code f x ⊆ code f c := by
  intro sub
  obtain ⟨w,xw,cw⟩ := together
  have incl (u) (hu : u∈residualUnits 14 D b) (xu : x∈supp 14 D u.1) : c∈supp 14 D u.1 := by
    obtain ⟨t,eq⟩ := f.surjective ⟨u,hu⟩
    have xt : t∈code f x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [eq] using xu⟩
    simpa [eq] using (Finset.mem_filter.mp (sub xt)).2
  obtain ⟨e0,other⟩ := ri_gen graph_ok h hc b hb ne elig incl (w:=w) ⟨xw,cw⟩
  obtain ⟨p,hp,q,hq,pq,mp,mq⟩ := miss
  by_cases ep : p=e0
  · exact mq (other q hq (by rintro rfl; exact pq ep))
  · exact mp (other p hp ep)

set_option maxHeartbeats 0 in
theorem code_excludes {k : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (b : V → Nat) (hb : PureBranch 14 D b) (f : Fin k ≃ ↥(residualUnits 14 D b)) (x c : V)
    (ne : x≠c) (elig : x∈eligSet 14 D) (miss : MissingTwo D x c) :
    code f x=∅ ∨ ¬code f x⊆code f c := by
  by_cases empty : code f x=∅
  · exact Or.inl empty
  right; intro sub
  obtain ⟨t,xt⟩ := Finset.nonempty_iff_ne_empty.mpr empty
  exact code_diff h hc b hb f x c ne elig miss ⟨_,(Finset.mem_filter.mp xt).2,(Finset.mem_filter.mp (sub xt)).2⟩ sub

namespace Resolution

abbrev Lit := Nat × Bool

abbrev Clause := List Lit

def neg (l : Lit) : Lit := (l.1,!l.2)

def Yes (v : Nat → Bool) (l : Lit) := v l.1 = l.2

def Holds (v : Nat → Bool) (c : Clause) := ∃ l∈c, Yes v l

def Valid (v : Nat → Bool) (F : Array Clause) := ∀ c∈F, Holds v c

theorem neg_iff (v : Nat → Bool) (l : Lit) : Yes v (neg l) ↔ ¬Yes v l := by
  simp only [Yes,neg]
  cases v l.1 <;> cases l.2 <;> decide
end Resolution

namespace Resolution

def key (l : Lit) : Nat := 2*l.1+l.2.toNat

theorem key_injective : Function.Injective key := by
  rintro ⟨n,b⟩ ⟨m,c⟩ eq
  cases b <;> cases c <;> simp [key,Bool.toNat] at eq ⊢ <;> omega

def insertBit (a : Nat) (l : Lit) := a ||| (2 ^ key l)

def initial : Clause → Nat
  | [] => 0
  | l::ls => insertBit (initial ls) (neg l)

theorem get_insert (a : Nat) (p x : Lit) :
    (insertBit a p).testBit (key x)=true ↔ a.testBit (key x)=true ∨ p=x := by
  simp [insertBit,Nat.testBit_two_pow,key_injective.eq_iff]

theorem get_initial {c : Clause} {x : Lit} (h : (initial c).testBit (key x)=true) :
    ∃ l∈c, neg l=x := by
  induction c with
  | nil => simp [initial] at h
  | cons l ls ih =>
    rcases (get_insert _ _ _).mp h with h|e
    · obtain ⟨t,ht,eq⟩ := ih h; exact ⟨t,List.mem_cons_of_mem _ ht,eq⟩
    · exact ⟨l,List.mem_cons_self,e⟩

def allowed (a : Nat) (p : Option Lit) (c : Clause) : Bool :=
  c.all fun l => some l == p || a.testBit (key (neg l))

theorem allowed_ok {v a p c} (sat : Holds v c) (forced : ∀ l, a.testBit (key l)=true → Yes v l)
    (ok : allowed a p c=true) : ∃ l, some l=p ∧ Yes v l := by
  obtain ⟨l,hl,hv⟩ := sat
  have bound := (List.all_eq_true.mp ok) l hl
  simp only [Bool.or_eq_true,beq_iff_eq] at bound
  rcases bound with eq|deny
  · exact ⟨l,eq,hv⟩
  · exact ((neg_iff v l).mp (forced _ deny) hv).elim
end Resolution

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

def countAt (D : Dag) (x : V) := (sem_W 14 D x).card

def cap (k I : Nat) (x : V) := if x∈mask I then 1 else 2+k

def Together (D : Dag) (x c : V) := ∃ w, x∈supp 14 D w ∧ c∈supp 14 D w

def SLabel (D : Dag) (p : Slot) (x : V) := x∈supp 14 D (src D p)

structure Layout (D : Dag) (k I : Nat) where
  wire : V → Nat → Slot
  edge : EdgeIdx → Slot
  reader : Bool → EdgeIdx → Nat
  branch : V → Nat
  order : Fin k ≃ ↥(residualUnits 14 D branch)
  pure : PureBranch 14 D branch
  limit : ∀ x, countAt D x ≤ cap k I x
  member : ∀ x j, wire x j ∈ sem_W 14 D x
  inject : ∀ x j k, j<countAt D x → k<countAt D x → wire x j=wire x k → j=k
  covers : ∀ x e, e∈sem_W 14 D x → ∃ j<countAt D x, wire x j=e
  reader_live : ∀ s e, reader s e < countAt D (endpoint s e)
  read : ∀ s e, wire (endpoint s e) (reader s e)=flip s (edge e)

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem construct_layout {k I : Nat} {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (bp : Bplus 14 D=11) (eq : mask I=ineligSet 14 D) (sizeI : (mask I).card=k+3) :
    Nonempty (Layout D k I) := by
  classical
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  have el := inelig_card_add 14 D
  have diff := card_residual h.1 b hb
  rw [←eq,sizeI] at el
  have count : Fintype.card ↥(residualUnits 14 D b)=k := by rw [Fintype.card_coe]; omega
  let f := (Fintype.equivFinOfCardEq count).symm
  have lim (x : V) : countAt D x ≤ cap k I x := by
    unfold cap countAt
    split
    · rename_i hx
      obtain ⟨p,_,_,_,_,_,sw,_⟩ := sem_inelig_consumer graph_ok h hc (eq ▸ hx)
      change sem_W 14 D x={p} at sw
      rw [sw,Finset.card_singleton]
    · have one := Finset.card_le_card (Finset.inter_subset_left : ({x}:Finset V)∩eligSet 14 D ⊆ {x})
      have two := Finset.card_filter_le (residualUnits 14 D b) (fun u => x∈supp 14 D u.1)
      have cc := sem_code_count graph_ok h hc b hb x
      simp only [Finset.card_singleton] at one
      omega
  have has (x : V) : 0<countAt D x := by
    obtain ⟨y,xy,_⟩ := graph_ok.2.2.2 x x
    obtain ⟨p,hp,_⟩ := sem_edge_slots graph_ok h.1 hc xy
    exact Finset.card_pos.mpr ⟨p,hp⟩
  let enum (x : V) : Fin (countAt D x) ≃ ↥(sem_W 14 D x) :=
    (Fintype.equivFinOfCardEq (by simp [countAt])).symm
  let atIdx (x : V) (j : Nat) : Fin (countAt D x) := if hj : j<countAt D x then ⟨j,hj⟩ else ⟨0,has x⟩
  let w (x : V) (j : Nat) := ((enum x) (atIdx x j)).val
  have onto (x : V) (e) (he : e∈sem_W 14 D x) : ∃ j<countAt D x, w x j=e := by
    obtain ⟨i,hf⟩ := (enum x).surjective ⟨e,he⟩
    exact ⟨i.val,i.isLt,by simpa [w,atIdx,i.isLt] using congrArg Subtype.val hf⟩
  obtain ⟨P,hp⟩ := get_slots h hc
  choose readAt spec using (fun s e => onto (endpoint s e) _ (hp s e))
  refine ⟨⟨w,P,readAt,b,f,hb,lim,fun x j => ((enum x) (atIdx x j)).property,?_,onto,fun s e => (spec s e).1,fun s e => (spec s e).2⟩⟩
  intro x j k hj hk same
  have e := (enum x).injective (Subtype.ext same)
  simpa [atIdx,hj,hk] using congrArg Fin.val e
namespace Layout
variable {D : Dag} {k I : Nat} (Z : Layout D k I)

def lab (x : V) (j : Nat) (c : V) := SLabel D (Z.wire x j) c

def edgeLabelAt (s : Bool) (e : EdgeIdx) (c : V) := SLabel D (flip s (Z.edge e)) c

def res (s : Fin k) (x : V) := x∈supp 14 D (Z.order s).val.1

def Live (_Z : Layout D k I) (x : V) (j : Nat) := j<countAt D x

def avoid (x : V) (A : Nat) (j : Nat) := Z.Live x j ∧ ∀ c∈mask A, ¬Z.lab x j c

def see (x i : V) (P : Nat) (j : Nat) := Z.Live x j ∧ ∀ c∈mask P, Z.lab x j c ↔ adj i c

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem expose (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) (A : Nat) (ind : independent (mask A))
    (ne : ∃ a∈mask A, adj x a) : ∃ j<cap k I x, Z.avoid x A j := by
  obtain ⟨g,s,hl,_,xl,no,dis⟩ := sem_exposure graph_ok h.1 hc (mask A) ind x ne
  obtain ⟨j,live,eq⟩ := Z.covers x (g,s) (sem_mem_W.mpr ⟨hl,xl,no⟩)
  exact ⟨j,lt_of_lt_of_le live (Z.limit x),live,fun c cin (hh : SLabel D (Z.wire x j) c) =>
    Finset.disjoint_left.mp dis (eq ▸ hh) cin⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem exact_slot (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (zero : Bzero 14 D=0)
    (eq : mask I=ineligSet 14 D) (x i : V) (P : Nat) (ind : independent (mask P))
    (geom : i∈mask I ∧ x∈mask P ∧ adj i x) : ∃ j<cap k I x, Z.see x i P j := by
  obtain ⟨e,he,hw⟩ := exact_position h hc zero (mask P) ind i x (eq ▸ geom.1) geom.2.1 geom.2.2
  obtain ⟨j,live,same⟩ := Z.covers x e he
  exact ⟨j,lt_of_lt_of_le live (Z.limit x),live,fun c inc => by simpa [lab,SLabel,same] using hw c inc⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem ri_slots (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x c : V) (neq : x≠c) (elig : x∈eligSet 14 D)
    {j l : Nat} (lt : j<l) (live : Z.Live x l) (com : Together D x c) :
    Z.lab x j c ∨ Z.lab x l c ∨ ∃ t : Fin k, Z.res t x ∧ ¬Z.res t c := by
  by_contra! bad
  rcases bad with ⟨mj,ml,rest⟩
  have hj : j<countAt D x := lt_trans lt live
  have miss : MissingTwo D x c := ⟨_,Z.member _ _,_,Z.member _ _,fun e => (Nat.ne_of_lt lt) (Z.inject x j l hj live e),mj,ml⟩
  have no := code_diff h hc Z.branch Z.pure Z.order x c neq elig miss com
  apply no
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,rest t (Finset.mem_filter.mp ht).2⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem size_code (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) :
    countAt D x ≤ 2 + (code Z.order x).card := by
  classical
  have image : (code Z.order x).image (fun t => (Z.order t).val) = (residualUnits 14 D Z.branch).filter (fun u => x∈supp 14 D u.1) := by
    ext u
    constructor
    · intro hu; obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hu
      exact Finset.mem_filter.mpr ⟨(Z.order t).property,(Finset.mem_filter.mp ht).2⟩
    · intro hu
      obtain ⟨base,supp⟩ := Finset.mem_filter.mp hu
      obtain ⟨t,e⟩ := Z.order.surjective ⟨u,base⟩
      exact Finset.mem_image.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa [e] using supp⟩,congrArg Subtype.val e⟩
  have cc := sem_code_count graph_ok h hc Z.branch Z.pure x
  have one := Finset.card_le_card (Finset.inter_subset_left : ({x}:Finset V)∩eligSet 14 D ⊆ {x})
  simp only [Finset.card_singleton] at one
  rw [←image,Finset.card_image_of_injective _ (fun _ _ e => Z.order.injective (Subtype.ext e))] at cc
  unfold countAt
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem mem_code (x : V) (s : Fin k) : s∈code Z.order x ↔ Z.res s x := by simp [code,res]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem some_code (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) (live : Z.Live x 2) :
    ∃ t, Z.res t x := by
  have sz := Z.size_code h hc x
  obtain ⟨t,mem⟩ := Finset.card_pos.mp (show 0<(code Z.order x).card by change 2<countAt D x at live; omega)
  exact ⟨t,(Z.mem_code _ _).mp mem⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem all_code (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (x : V) (live : Z.Live x (1+k)) :
    ∀ t, Z.res t x := by
  have sz := Z.size_code h hc x
  change 1+k<countAt D x at live
  have full : code Z.order x=Finset.univ := Finset.eq_univ_of_card _ (by simp; have := Finset.card_le_univ (code Z.order x); simp at this; omega)
  exact fun t => (Z.mem_code x t).1 (full ▸ Finset.mem_univ t)
end Layout
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools Resolution

theorem together_comm (D : Dag) (x c : V) : Together D x c ↔ Together D c x := by
  simp only [Together,and_comm]
namespace Layout
variable {D : Dag} {k I : Nat} (Z : Layout D k I)

theorem selfLab (x : V) (j : Nat) : Z.lab x j x := (sem_mem_W.mp (Z.member x j)).2.1

theorem commonLab (x c : V) (j : Nat) (h : Z.lab x j c) : Together D x c :=
  ⟨_,Z.selfLab x j,h⟩

theorem commonRes (s : Fin k) (x c : V) (u : Z.res s x) (v : Z.res s c) : Together D x c := ⟨_,u,v⟩

theorem readerLab (s : Bool) (e : EdgeIdx) (j : Nat) (c : V) (x : V) (ep : endpoint s e=x)
    (q : Z.reader s e=j) : Z.lab x j c ↔ Z.edgeLabelAt s e c := by
  subst x j
  unfold lab edgeLabelAt
  rw [Z.read]

theorem readerEq (s : Bool) (i k : EdgeIdx) (j : Nat) (ep : endpoint s i=endpoint s k)
    (qi : Z.reader s i=j) (qk : Z.reader s k=j) : Z.edge i=Z.edge k := by
  apply flip_inj s
  rw [←Z.read,←Z.read,qi,qk,ep]

theorem boundReader (s : Bool) (e : EdgeIdx) : Z.reader s e<cap k I (endpoint s e) :=
  lt_of_lt_of_le (Z.reader_live s e) (Z.limit _)

theorem eqLab (s : Bool) (i j : EdgeIdx) (c : V) (eq : Z.edge i=Z.edge j) : Z.edgeLabelAt s i c ↔ Z.edgeLabelAt s j c := by
  simp [edgeLabelAt,eq]
end Layout
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

inductive Fact where
  | live (x : V) (j : Nat)
  | lab (x : V) (j : Nat) (c : V)
  | res (t : Nat) (x : V)
  | common (x c : V)
  | gate (e f : EdgeIdx)
  | reader (s : Bool) (e : EdgeIdx) (j : Nat)
  | es (s : Bool) (e : EdgeIdx) (c : V)
  | avoid (x : V) (a j : Nat)
  | see (x i : V) (p j : Nat)
  | diff (t : Nat) (x c : V)
  deriving DecidableEq, Inhabited

abbrev FactClause := List (Fact × Bool)

def rAt {D : Dag} {k I : Nat} (Z : Layout D k I) (s : Nat) (x : V) :=
  ∃ t : Fin k, t.val=s ∧ Z.res t x

def evalFact {D : Dag} {k I : Nat} (Z : Layout D k I) : Fact → Prop
  | .live x j => Z.Live x j
  | .lab x j c => Z.lab x j c
  | .res t x => rAt Z t x
  | .common x c => Together D x c
  | .gate i j => Z.edge i=Z.edge j
  | .reader s e j => Z.reader s e=j
  | .es s e c => Z.edgeLabelAt s e c
  | .avoid x a j => Z.avoid x a j
  | .see x i p j => Z.see x i p j
  | .diff t x c => rAt Z t x ∧ ¬rAt Z t c

def EvalClause {D : Dag} {k I : Nat} (Z : Layout D k I) (c : FactClause) : Prop :=
  ∃ e∈c, if e.2 then evalFact Z e.1 else ¬evalFact Z e.1

abbrev pos (a : Fact) : Fact × Bool := (a,true)

abbrev negF (a : Fact) : Fact × Bool := (a,false)

def anyRange (n : Nat) (p : Nat → Fact) : FactClause := (List.range n).map (fun j => pos (p j))

theorem pos_iff {D : Dag} {k I} (Z : Layout D k I) (a : Fact) (c : FactClause) :
    EvalClause Z (pos a::c) ↔ evalFact Z a ∨ EvalClause Z c := by
  simp [EvalClause,List.mem_cons,exists_or,or_and_right]

theorem neg_iff {D : Dag} {k I} (Z : Layout D k I) (a : Fact) (c : FactClause) :
    EvalClause Z (negF a::c) ↔ ¬evalFact Z a ∨ EvalClause Z c := by
  simp [EvalClause,List.mem_cons,exists_or,or_and_right]

theorem none_iff {D : Dag} {k I} (Z : Layout D k I) : ¬EvalClause Z [] := by simp [EvalClause]

theorem range_iff {D : Dag} {k I} (Z : Layout D k I) (n : Nat) (p : Nat → Fact) :
    EvalClause Z (anyRange n p) ↔ ∃ j<n, evalFact Z (p j) := by
  simp [EvalClause,anyRange]

theorem atRes {D : Dag} {k I} (Z : Layout D k I) (t : Fin k) (x : V) : rAt Z t.val x ↔ Z.res t x := by
  constructor
  · rintro ⟨s,e,h⟩; exact (Fin.ext e : s=t) ▸ h
  · exact fun h => ⟨t,rfl,h⟩

inductive Scheme where
  | self (x : V) (j : Nat)
  | earlier (x : V) (j : Nat)
  | labCommon (x c : V) (j : Nat)
  | someRes (x : V)
  | allRes (x : V) (t : Nat)
  | exposure (x : V) (a : Nat)
  | exactAt (x i : V) (p : Nat)
  | avoidLive (x : V) (a j : Nat)
  | seeLive (x i : V) (p j : Nat)
  | avoidNot (x c : V) (a j : Nat)
  | seeLab (x i c : V) (p j : Nat)
  | diffX (t : Nat) (x c : V)
  | diffC (t : Nat) (x c : V)
  | adjacentCommon (x c i : V)
  | resCommon (x c : V) (t : Nat)
  | residual (x c : V) (j l : Nat)
  | readerAny (s : Bool) (e : EdgeIdx)
  | readerLive (s : Bool) (e : EdgeIdx) (j : Nat)
  | readerLab (s : Bool) (e : EdgeIdx) (j : Nat) (c : V) (forward : Bool)
  | eqLab (s : Bool) (e f : EdgeIdx) (c : V) (forward : Bool)
  | gateEq (s : Bool) (e f : EdgeIdx) (j : Nat)
  deriving Inhabited

def commonF (x c : V) := Fact.common (min x c) (max x c)

theorem commonF_iff {D : Dag} {k I} (Z : Layout D k I) (x c : V) : evalFact Z (commonF x c) ↔ Together D x c := by
  rcases le_total x c with le|le
  · simp [commonF,min_eq_left le,max_eq_right le,evalFact]
  · simp [commonF,min_eq_right le,max_eq_left le,evalFact,together_comm D c x]

def enabled (k I : Nat) : Scheme → Bool
  | .allRes _ t => decide (t<k)
  | .exposure x a => decide (independent (mask a) ∧ ∃ v∈mask a, adj x v)
  | .exactAt x i p => decide (independent (mask p) ∧ i∈mask I ∧ x∈mask p ∧ adj i x)
  | .avoidNot _ c a _ => decide (c∈mask a)
  | .seeLab _ _ c p _ => decide (c∈mask p)
  | .adjacentCommon x c i => decide (i∈mask I ∧ adj i x ∧ adj i c)
  | .residual x c j l => decide (x≠c ∧ x∉mask I ∧ j<l)
  | .gateEq s e f _ => decide (endpoint s e=endpoint s f)
  | _ => true

def expand (k I : Nat) : Scheme → FactClause
  | .self x j => [pos (.lab x j x)]
  | .earlier x j => [negF (.live x (j+1)),pos (.live x j)]
  | .labCommon x c j => [negF (.live x j),negF (.lab x j c),pos (commonF x c)]
  | .someRes x => negF (.live x 2)::anyRange k (fun t => .res t x)
  | .allRes x t => [negF (.live x (1+k)),pos (.res t x)]
  | .exposure x a => anyRange (cap k I x) (fun j => .avoid x a j)
  | .exactAt x i p => anyRange (cap k I x) (fun j => .see x i p j)
  | .avoidLive x a j => [negF (.avoid x a j),pos (.live x j)]
  | .seeLive x i p j => [negF (.see x i p j),pos (.live x j)]
  | .avoidNot x c a j => [negF (.avoid x a j),negF (.lab x j c)]
  | .seeLab x i c p j => if adj i c then [negF (.see x i p j),pos (.lab x j c)] else [negF (.see x i p j),negF (.lab x j c)]
  | .diffX t x c => [negF (.diff t x c),pos (.res t x)]
  | .diffC t x c => [negF (.diff t x c),negF (.res t c)]
  | .adjacentCommon x c _ => [pos (commonF x c)]
  | .resCommon x c t => [negF (.res t x),negF (.res t c),pos (commonF x c)]
  | .residual x c j l => negF (commonF x c)::negF (.live x l)::pos (.lab x j c)::pos (.lab x l c)::anyRange k (fun t => .diff t x c)
  | .readerAny s e => anyRange (cap k I (endpoint s e)) (fun j => .reader s e j)
  | .readerLive s e j => [negF (.reader s e j),pos (.live (endpoint s e) j)]
  | .readerLab s e j c dir => [(Fact.reader s e j,false),(.lab (endpoint s e) j c,!dir),(.es s e c,dir)]
  | .eqLab s e f c dir => [(Fact.gate e f,false),(.es s e c,!dir),(.es s f c,dir)]
  | .gateEq s e f j => [negF (.reader s e j),negF (.reader s f j),pos (.gate e f)]

theorem scheme_sound {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (q : Scheme) (en : enabled k I q=true) : EvalClause Z (expand k I q) := by
  classical
  cases q with
  | self x j =>
    simpa only [expand,pos_iff,none_iff,or_false,evalFact] using Z.selfLab x j
  | earlier x j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact,Layout.Live]
    omega
  | labCommon x c j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,commonF_iff]
    simp only [evalFact]
    have := Z.commonLab x c j; tauto
  | someRes x =>
    simp only [expand,neg_iff,range_iff,evalFact]
    by_cases active : Z.Live x 2
    · obtain ⟨t,ht⟩ := Z.some_code h hc x active
      exact Or.inr ⟨t.val,t.isLt,(atRes Z t x).2 ht⟩
    · exact Or.inl active
  | allRes x t =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases active : Z.Live x (1+k)
    · let i : Fin k := ⟨t,en⟩
      exact Or.inr ((atRes Z i x).2 (Z.all_code h hc x active i))
    · exact Or.inl active
  | exposure x a =>
    simp only [enabled,decide_eq_true_eq] at en
    exact (range_iff _ _ _).2 (Z.expose h hc x a en.1 en.2)
  | exactAt x i p =>
    simp only [enabled,decide_eq_true_eq] at en
    exact (range_iff _ _ _).2 (Z.exact_slot h hc z eq x i p en.1 en.2)
  | avoidLive x a j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases v : Z.avoid x a j; exact Or.inr v.1; exact Or.inl v
  | seeLive x i p j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases v : Z.see x i p j; exact Or.inr v.1; exact Or.inl v
  | avoidNot x c a j =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,none_iff,or_false,evalFact]
    by_cases v : Z.avoid x a j; exact Or.inr (v.2 c en); exact Or.inl v
  | seeLab x i c p j =>
    simp only [enabled,decide_eq_true_eq] at en
    by_cases a : adj i c <;> simp only [expand,a,if_true,if_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    · by_cases v : Z.see x i p j; exact Or.inr ((v.2 c en).2 a); exact Or.inl v
    · by_cases v : Z.see x i p j; exact Or.inr (fun u => a ((v.2 c en).1 u)); exact Or.inl v
  | diffX t x c => simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]; tauto
  | diffC t x c => simp only [expand,neg_iff,none_iff,or_false,evalFact]; tauto
  | adjacentCommon x c i =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,pos_iff,none_iff,or_false,commonF_iff]
    exact share h hc (i:=i) (eq ▸ en.1) en.2.1 en.2.2
  | resCommon x c t =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,commonF_iff]
    simp only [evalFact]
    by_cases rx : rAt Z t x <;> by_cases rc : rAt Z t c
    · obtain ⟨i,eqi,hx⟩ := rx; obtain ⟨j,eqj,hc⟩ := rc
      have same : i=j := Fin.ext (eqi.trans eqj.symm)
      exact Or.inr (Or.inr (Z.commonRes i x c hx (same ▸ hc)))
    all_goals tauto
  | residual x c j l =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,commonF_iff,range_iff]
    simp only [evalFact]
    by_cases com : Together D x c
    · right; by_cases active : Z.Live x l
      · right
        have elig : x∈eligSet 14 D := by by_contra no; exact en.2.1 (eq ▸ sem_mem_inelig.mpr no)
        rcases Z.ri_slots h hc x c en.1 elig en.2.2 active com with v|v|⟨t,hx,miss⟩
        · exact Or.inl v
        · exact Or.inr (Or.inl v)
        · exact Or.inr (Or.inr ⟨t.val,t.isLt,(atRes Z t x).2 hx,fun u => miss ((atRes Z t c).1 u)⟩)
      · exact Or.inl active
    · exact Or.inl com
  | readerAny s e => exact (range_iff _ _ _).2 ⟨_,Z.boundReader s e,rfl⟩
  | readerLive s e j =>
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    by_cases r : Z.reader s e=j; exact Or.inr (r ▸ Z.reader_live s e); exact Or.inl r
  | readerLab s e j c dir =>
    cases dir <;> change EvalClause Z (negF _ :: _)
    all_goals simp only [Bool.not_true,Bool.not_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    all_goals by_cases r : Z.reader s e=j
    all_goals first | exact Or.inl r | have v := Z.readerLab s e j c _ rfl r; tauto
  | eqLab s e f c dir =>
    cases dir <;> change EvalClause Z (negF _ :: _)
    all_goals simp only [Bool.not_true,Bool.not_false,neg_iff,pos_iff,none_iff,or_false,evalFact]
    all_goals by_cases r : Z.edge e=Z.edge f
    all_goals first | exact Or.inl r | have v := Z.eqLab s e f c r; tauto
  | gateEq s e f j =>
    simp only [enabled,decide_eq_true_eq] at en
    simp only [expand,neg_iff,pos_iff,none_iff,or_false,evalFact]
    have v := Z.readerEq s e f j en
    tauto
end Compact

namespace Resolution

def firstOpen (a : Nat) (c : Clause) : Option Lit :=
  c.find? fun l => !(a.testBit (key (neg l)))

def runHints (F : Array Clause) (last : Nat) : List Nat → Nat → Bool
  | [], a => if h : last<F.size then allowed a none F[last] else false
  | i::rest, a => if h : i<F.size then
      match firstOpen a F[i] with
      | none => allowed a none F[i]
      | some p => allowed a (some p) F[i] && runHints F last rest (insertBit a p)
    else false

theorem runHints_sound {F v} (sat : Valid v F) (last : Nat) (units : List Nat) (a : Nat)
    (forced : ∀ l, a.testBit (key l)=true → Yes v l) (ok : runHints F last units a=true) : False := by
  induction units generalizing a with
  | nil =>
    simp only [runHints] at ok
    split at ok
    · rename_i h
      obtain ⟨_,e,_⟩ := allowed_ok (sat _ (Array.getElem_mem h)) forced ok
      contradiction
    · contradiction
  | cons i is ih =>
    simp only [runHints] at ok
    split at ok
    · rename_i h
      split at ok
      · obtain ⟨_,e,_⟩ := allowed_ok (sat _ (Array.getElem_mem h)) forced ok
        contradiction
      · rename_i p _
        rw [Bool.and_eq_true] at ok
        obtain ⟨l,e,hv⟩ := allowed_ok (sat _ (Array.getElem_mem h)) forced ok.1
        have eq := Option.some.inj e
        subst l
        apply ih (insertBit a p) _ ok.2
        intro t ht
        rcases (get_insert _ _ _).1 ht with old | rfl
        · exact forced t old
        · exact hv
    · contradiction

abbrev SmallLine := Clause × Nat × List Nat

def hintGrow (F : Array Clause) : List SmallLine → Array Clause
  | [] => F
  | l::ls => hintGrow (F.push l.1) ls

def validHints (F : Array Clause) : List SmallLine → Bool
  | [] => true
  | l::ls => runHints F l.2.1 l.2.2 (initial l.1) && validHints (F.push l.1) ls

theorem checkedHints {F v} (sat : Valid v F) (ls : List SmallLine) (ok : validHints F ls=true) :
    Valid v (hintGrow F ls) := by
  induction ls generalizing F with
  | nil => exact sat
  | cons l ls ih =>
    simp only [validHints,Bool.and_eq_true] at ok
    obtain ⟨t,r⟩ := ok
    have holds : Holds v l.1 := by
      by_contra no
      apply runHints_sound sat _ _ _ _ t
      intro x hx
      obtain ⟨y,hy,rfl⟩ := get_initial hx
      exact (neg_iff v y).2 (fun yes => no ⟨y,hy,yes⟩)
    apply ih (F:=F.push l.1) _ r
    intro c hc
    rcases Array.mem_push.mp hc with hc|hc
    · exact sat _ hc
    · exact hc ▸ holds

theorem finalHints {F v} (sat : Valid v F) (last : Nat) (hints : List Nat)
    (h : runHints F last hints 0=true) : False := runHints_sound sat last hints 0 (by simp) h

def digits (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | count+1, n => (n % (2^width)) :: digits width count (n >>> width)

def unpackLits (width len bits : Nat) : Clause :=
  (digits width len bits).map (fun n => (n/2,n%2==1))
end Resolution

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools
open Resolution

def atLit (a : Array Fact) (l : Lit) : Fact × Bool := (a[l.1]?.getD default,l.2)

def localCheck (k I : Nat) (a : Array Fact) (r : Scheme) (c : Clause) : Bool :=
  enabled k I r && (expand k I r).all (fun p => (c.map (atLit a)).contains p)

def inputsOK (k I : Nat) (a : Array Fact) : List Scheme → List Clause → Bool
  | [],[] => true
  | r::rs,c::cs => localCheck k I a r c && inputsOK k I a rs cs
  | _,_ => false

noncomputable def truth {D : Dag} {k I} (Z : Layout D k I) (a : Array Fact) (n : Nat) :=
  @decide (evalFact Z (a[n]?.getD default)) (Classical.propDecidable _)

theorem localSound {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (r : Scheme) (c : Clause) (ok : localCheck k I a r c=true) :
    Holds (truth Z a) c := by
  simp only [localCheck,Bool.and_eq_true] at ok
  obtain ⟨p,hm,hval⟩ := scheme_sound Z h hc z eq r ok.1
  have mem := List.contains_iff_mem.mp (List.all_eq_true.mp ok.2 p hm)
  obtain ⟨l,hl,eqp⟩ := List.mem_map.mp mem
  subst p
  refine ⟨l,hl,?_⟩
  rcases l with ⟨i,b⟩
  cases b <;> simp [truth,Yes,atLit] at hval ⊢ <;> exact hval

theorem inputs_sound {D : Dag} {k I : Nat} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (F : Array Clause)
    (ok : inputsOK k I a R F.toList=true) : Valid (truth Z a) F := by
  have all (rs : List Scheme) (cs : List Clause) (good : inputsOK k I a rs cs=true) : List.Forall (Holds (truth Z a)) cs := by
    induction rs generalizing cs with
    | nil => cases cs <;> simp_all [inputsOK,List.Forall]
    | cons r rs ih =>
      cases cs with
      | nil => contradiction
      | cons c cs =>
        simp only [inputsOK,Bool.and_eq_true] at good
        apply List.forall_iff_forall_mem.mpr
        intro item mem
        rcases List.mem_cons.mp mem with rfl|rest
        · exact localSound Z h hc z eq a r _ good.1
        · exact List.forall_iff_forall_mem.mp (ih cs good.2) item rest
  intro c cF
  exact List.forall_iff_forall_mem.mp (all R F.toList ok) c (Array.mem_toList_iff.mpr cF)
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools Resolution

def readClause (width n : Nat) : Clause := unpackLits width (n%8) (n>>>3)

def readStep (clauseWidth reasonWidth g u : Nat) : SmallLine :=
  (unpackLits clauseWidth (g%64) (g>>>6), (u>>>9) % (2^reasonWidth), digits reasonWidth (u%512) (u>>>(9+reasonWidth)))
end Compact

namespace Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools Resolution

def ValidThrough (v : Nat → Bool) (book : Nat → Clause) (n : Nat) :=
  ∀ i, i<n → Holds v (book i)

def checkReasons (book : Nat → Clause) (n last : Nat) : List Nat → Nat → Bool
  | [], a => decide (last<n) && allowed a none (book last)
  | i::rest, a => decide (i<n) &&
      match firstOpen a (book i) with
      | none => allowed a none (book i)
      | some p => allowed a (some p) (book i) && checkReasons book n last rest (insertBit a p)

theorem reasons_sound {v book n} (sat : ValidThrough v book n)
    (last : Nat) (units : List Nat) (a : Nat)
    (forced : ∀ l, a.testBit (key l)=true → Yes v l)
    (ok : checkReasons book n last units a=true) : False := by
  induction units generalizing a with
  | nil =>
    simp only [checkReasons,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨_,e,_⟩ := allowed_ok (sat _ ok.1) forced ok.2
    contradiction
  | cons i us ih =>
    simp only [checkReasons,Bool.and_eq_true,decide_eq_true_eq] at ok
    obtain ⟨hi,rest⟩ := ok
    split at rest
    · obtain ⟨_,e,_⟩ := allowed_ok (sat _ hi) forced rest
      contradiction
    · rename_i p _
      rw [Bool.and_eq_true] at rest
      obtain ⟨l,e,hv⟩ := allowed_ok (sat _ hi) forced rest.1
      have eq := Option.some.inj e
      subst l
      apply ih (insertBit a p) _ rest.2
      intro t ht
      rcases (get_insert _ _ _).1 ht with old|rfl
      · exact forced t old
      · exact hv

def checkRows (book : Nat → Clause) (width : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | i, u::us => checkReasons book i ((u>>>9) % (2^width))
      (digits width (u%512) (u>>>(9+width))) (initial (book i)) && checkRows book width (i+1) us

theorem rows_sound {v book width i} (sat : ValidThrough v book i) (rows : List Nat)
    (ok : checkRows book width i rows=true) : ValidThrough v book (i+rows.length) := by
  induction rows generalizing i with
  | nil => simpa using sat
  | cons u us ih =>
    simp only [checkRows,Bool.and_eq_true] at ok
    have holds : Holds v (book i) := by
      by_contra no
      apply reasons_sound sat _ _ _ _ ok.1
      intro x hx
      obtain ⟨y,hy,rfl⟩ := get_initial hx
      exact (Resolution.neg_iff v y).2 (fun yes => no ⟨y,hy,yes⟩)
    have step : ValidThrough v book (i+1) := by
      intro j hj
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with lt | rfl
      · exact sat j lt
      · exact holds
    have next := ih step ok.2
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using next

def baseBook (book : Nat → Clause) (n : Nat) : Array Clause :=
  Array.ofFn fun i : Fin n => book i.val

theorem book_start {D k I} (Z : Layout D k I) (h : StrictLive 14 D)
    (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (eq : mask I=ineligSet 14 D)
    (a : Array Fact) (R : List Scheme) (book : Nat → Clause) (n : Nat)
    (ok : inputsOK k I a R (baseBook book n).toList=true) : ValidThrough (truth Z a) book n := by
  have sat := inputs_sound Z h hc z eq a R (baseBook book n) ok
  intro j hj
  apply sat
  exact Array.mem_ofFn.mpr ⟨⟨j,hj⟩,rfl⟩

theorem book_end {v book n} (sat : ValidThrough v book n) (last : Nat) (units : List Nat)
    (ok : checkReasons book n last units 0=true) : False :=
  reasons_sound sat last units 0 (by simp) ok
end Compact

end PEqualNP.Outside.L_meta_9775.UpstreamCore
