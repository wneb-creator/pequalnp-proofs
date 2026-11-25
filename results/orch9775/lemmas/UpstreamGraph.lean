import UpstreamDagTools

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

def edges : List (Nat × Nat) := [(0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 13), (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12), (6, 8), (6, 9), (6, 11)]

def hit (x : Fin 14 → Bool) := ∃ u v : Fin 14, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true

def computes (C : Circuit) := ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = true ↔ hit x

theorem input_bit {n} (x : Fin n → Bool) (i : Fin n) : (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.MetaComplexity PEqualNP.CircuitLowerBounds

abbrev V := Fin 14

def neigh (v : V) : Nat := [1280, 8832, 8448, 6272, 11264, 5632, 2816, 10, 69, 98, 49, 88, 40, 22].getD v.val 0

def adj (u v : V) : Prop := (neigh u).testBit v.val = true

instance (u v : V) : Decidable (adj u v) := inferInstanceAs (Decidable ((neigh u).testBit v.val = true))

theorem graph_ok : sem_Gr adj := by unfold sem_Gr; decide +kernel

theorem graph_edges : ∀ u v : V, adj u v ↔ (u.val,v.val)∈edges ∨ (v.val,u.val)∈edges := by decide +kernel

theorem agrees (x : V → Bool) : hit x ↔ sem_Edge adj x := by
  constructor
  · rintro ⟨u,v,e,hu,hv⟩
    exact ⟨u,v,(graph_edges u v).2 (Or.inl e),hu,hv⟩
  · rintro ⟨u,v,a,hu,hv⟩
    rcases (graph_edges u v).1 a with e|e
    · exact ⟨u,v,e,hu,hv⟩
    · exact ⟨v,u,e,hv,hu⟩

theorem empty_bad : ¬hit (fun _ => false) := by rintro ⟨_,_,_,h,_⟩; contradiction

theorem single_bad (i : V) : ¬hit (single i) := fun h => sem_single_no_edge graph_ok i ((agrees _).mp h)

theorem normalized (C : Circuit) (hm : Monotone2 C) (hc : computes C) :
    ∃ D : Dag, StrictLive 14 D ∧ D.length ≤ C.size ∧ sem_Comp 14 adj D := by
  obtain ⟨D,hd,le,ev⟩ := normalize_strictLive (n:=14) C hm (by
    intro b
    cases b
    · refine ⟨fun _ => true,?_⟩
      rw [Ne, Bool.not_eq_false]
      exact (hc _).2 ⟨0,8,by decide,rfl,rfl⟩
    · exact ⟨fun _ => false,fun h => empty_bad ((hc _).1 h)⟩) (by
    intro i
    exact ⟨single i,fun h => single_bad i ((hc _).1 (by rw [h]; simp [single]))⟩) (by
    intro i
    obtain ⟨j,ij,ne⟩ := graph_ok.2.2.2 i i
    refine ⟨single j,sem_two i j,?_,?_⟩
    · intro k hki; simp [sem_two,single,hki]
    · intro h
      exact single_bad j ((hc _).1 (h.trans ((hc _).2 ((agrees _).2 (sem_two_edge ij))))))
  exact ⟨D,hd,le,fun x => by rw [ev,hc]; exact agrees x⟩

def mask (m : Nat) : Finset V := Finset.univ.filter (fun v => m.testBit v.val)

def independent (T : Finset V) : Prop := ∀ a ∈ T, ∀ b ∈ T, ¬adj a b

instance (T : Finset V) : Decidable (independent T) := inferInstanceAs (Decidable (∀ a ∈ T, ∀ b ∈ T, ¬adj a b))

def ValidPrivate (T J : Finset V) (A : V → Finset V) : Prop :=
  (∀ i ∈ J, (∃ a ∈ T, adj i a) ∧ ∀ f ∈ T, ∃ a ∈ A f, adj i a) ∧
  (∀ f ∈ T, independent (A f) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, adj f a)

instance (T J : Finset V) (A : V → Finset V) : Decidable (ValidPrivate T J A) := by unfold ValidPrivate; infer_instance

def cost (D : Dag) (T : Finset V) := (merges 14 D (carrierT 14 D T)).card

theorem bound_rule {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (T J : Finset V) (A : V → Finset V) (valid : ValidPrivate T J A)
    (hJ : J⊆ineligSet 14 D) (m k : Nat) (hm : m≤cost D T) (hk : k+T.card ≤ J.card+m) :
    (eligSet 14 D).card+k ≤ Bplus 14 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨pos,hpos⟩ := k4_assigned graph_ok h hc
  have ex := tri_exits graph_ok h.1 hc hpos T J A
    (fun i hi => ⟨hJ hi,(valid.1 i hi).1,(valid.1 i hi).2⟩) valid.2
  have cap := k4_budget graph_ok h hc b hb T
  unfold cost at hm
  omega

theorem share {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    {i x y : V} (hi : i∈ineligSet 14 D) (hx : adj i x) (hy : adj i y) :
    ∃ w : Nat, x∈supp 14 D w ∧ y∈supp 14 D w := by
  obtain ⟨e,_,_,_,_,hn,_⟩ := sem_inelig_consumer graph_ok h hc hi
  exact ⟨_,hn x hx,hn y hy⟩

theorem cost_one {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (T : Finset V) (i x y : V) (hi : i∈ineligSet 14 D)
    (geom : adj i x ∧ adj i y ∧ x∈T ∧ y∈T ∧ x≠y) : 1≤cost D T := by
  obtain ⟨w,hx,hy⟩ := share h hc hi geom.1 geom.2.1
  obtain ⟨j,hj,_⟩ := k4_mask_gate h.1 T w (Finset.one_lt_card.mpr
    ⟨x,Finset.mem_inter.mpr ⟨hx,geom.2.2.1⟩,y,Finset.mem_inter.mpr ⟨hy,geom.2.2.2.1⟩,geom.2.2.2.2⟩)
  exact Finset.card_pos.mpr ⟨j,hj⟩

theorem cost_two {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (T : Finset V) (i j x y z : V) (hi : i∈ineligSet 14 D) (hj : j∈ineligSet 14 D)
    (geom : adj i x ∧ adj i y ∧ adj j x ∧ adj j z ∧ T.card=3 ∧ x∈T ∧ y∈T ∧ z∈T ∧ x≠y ∧ x≠z ∧ y≠z) :
    2≤cost D T := by
  rcases geom with ⟨ix,iy,jx,jz,t3,xt,yt,zt,xy,xz,yz⟩
  obtain ⟨w,hx,hy⟩ := share h hc hi ix iy
  obtain ⟨v,hx',hz⟩ := share h hc hj jx jz
  exact k4_pair_merges h.1 t3 xt yt zt xy xz yz hx hy hx' hz

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

def projected (P : Finset V) (i : V) := P.filter (adj i)

set_option maxHeartbeats 0 in
theorem occurs {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hz : Bzero 14 D = 0)
    (P : Finset V) (hind : independent P) (i : V) (hi : i∈ineligSet 14 D) :
    sup_Occ 14 D P (projected P i) := by
  obtain ⟨j,s,_,_,_,ex⟩ := sem_exact_nbhd graph_ok h.1 hc P hind (sem_noempty_chain_out graph_ok h hc hz hi)
  refine ⟨src D (j,s),?_⟩
  ext a
  simp only [Finset.mem_inter,projected,Finset.mem_filter]
  constructor
  · rintro ⟨ha,hin⟩; exact ⟨hin,(ex a hin).1 ha⟩
  · rintro ⟨hin,ha⟩; exact ⟨(ex a hin).2 ha,hin⟩

set_option maxHeartbeats 0 in
theorem full_cost {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (hz : Bzero 14 D=0)
    (P I : Finset V) (hind : independent P) (sub : I ⊆ ineligSet 14 D)
    (L X : Finset (Finset V)) (P7 : P.card≤7)
    (tri : ∀ T∈L, T.card=3)
    (distinct : ∀ T∈L, ∀ U∈L, T≠U → (T∩U).card≤1)
    (cover : ∀ M∈L∪X, ∃ i∈I, projected P i=M)
    (pairs : ∀ M∈X, M.card=2 ∧ M∉L ∧ ∀ T∈L, ¬M⊆T)
    (conn : ∀ i∈I, ∃ a∈P, adj i a) :
    2*L.card + X.card + I.card + (eligSet 14 D).card ≤ 2*P.card+Bplus 14 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨pos,hpos⟩ := k4_assigned graph_ok h hc
  have occ (M) (hm : M∈L∪X) : sup_Occ 14 D P M := by
    obtain ⟨i,hi,rfl⟩ := cover _ hm
    exact occurs h hc hz P hind i (sub hi)
  have u := sup_charge h.1 P7 L (fun T ht => ⟨tri T ht,occ T (Finset.mem_union_left _ ht)⟩) distinct X (fun M hm => by
    obtain ⟨c,nl,nt⟩ := pairs M hm
    exact ⟨occ M (Finset.mem_union_right _ hm),by omega,nl,by omega,by omega,fun _ => nt⟩)
  have v : (sup_big 14 D P).card ≤ (merges 14 D (carrierT 14 D P)).card := Finset.card_le_card (Finset.filter_subset _ _ : sup_big 14 D P ⊆ merges 14 D (carrierT 14 D P))
  obtain ⟨ex,eq⟩ := k4_exits_ge hpos P I (fun i hi => ⟨sub hi,conn _ hi⟩)
  have w := Finset.card_le_card ex
  have cap := k4_budget graph_ok h hc b hb P
  omega

set_option maxHeartbeats 0 in
theorem side127 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (hz : Bzero 14 D=0) (sub : mask 127 = ineligSet 14 D) : 12≤Bplus 14 D := by
  let P := mask 16256
  let I := mask 127
  let L : Finset (Finset V) := {mask 8832,mask 6272,mask 11264,mask 5632,mask 2816}
  let X : Finset (Finset V) := {mask 1280,mask 8448}
  have hsub : I ⊆ ineligSet 14 D := sub ▸ Finset.Subset.rfl
  have tri : ∀ T∈L, T.card=3 := by
    intro T ht; simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have distinct : ∀ T∈L, ∀ U∈L, T≠U → (T∩U).card≤1 := by
    intro T ht U hu
    simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hits : ∀ M∈L∪X, ∃ i∈I, projected P i=M := by
    intro M hm; simp only [L,X,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact ⟨1,by decide +kernel,by decide +kernel⟩
    · exact ⟨3,by decide +kernel,by decide +kernel⟩
    · exact ⟨4,by decide +kernel,by decide +kernel⟩
    · exact ⟨5,by decide +kernel,by decide +kernel⟩
    · exact ⟨6,by decide +kernel,by decide +kernel⟩
    · exact ⟨0,by decide +kernel,by decide +kernel⟩
    · exact ⟨2,by decide +kernel,by decide +kernel⟩
  have sep : ∀ M∈X, M.card=2 ∧ M∉L ∧ ∀ T∈L, ¬M⊆T := by
    intro M hm; simp only [X,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> refine ⟨by decide +kernel,by decide +kernel,?_⟩ <;>
      intro T ht <;> simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht <;> rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have u := full_cost h hc hz P I (by decide +kernel) hsub L X (by decide +kernel)
    tri distinct hits sep (by decide +kernel)
  have c : P.card=7 ∧ I.card=7 ∧ L.card=5 ∧ X.card=2 := by decide +kernel
  have ec := inelig_card_add 14 D
  rw [←sub] at ec
  change I.card + _ = _ at ec
  omega

set_option maxHeartbeats 0 in
theorem side16256 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (hz : Bzero 14 D=0) (sub : mask 16256 = ineligSet 14 D) : 12≤Bplus 14 D := by
  let P := mask 127
  let I := mask 16256
  let L : Finset (Finset V) := {mask 69,mask 98,mask 49,mask 88,mask 22}
  let X : Finset (Finset V) := {mask 10,mask 40}
  have hsub : I ⊆ ineligSet 14 D := sub ▸ Finset.Subset.rfl
  have tri : ∀ T∈L, T.card=3 := by
    intro T ht; simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have distinct : ∀ T∈L, ∀ U∈L, T≠U → (T∩U).card≤1 := by
    intro T ht U hu
    simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht hu
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> rcases hu with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have hits : ∀ M∈L∪X, ∃ i∈I, projected P i=M := by
    intro M hm; simp only [L,X,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with (rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact ⟨8,by decide +kernel,by decide +kernel⟩
    · exact ⟨9,by decide +kernel,by decide +kernel⟩
    · exact ⟨10,by decide +kernel,by decide +kernel⟩
    · exact ⟨11,by decide +kernel,by decide +kernel⟩
    · exact ⟨13,by decide +kernel,by decide +kernel⟩
    · exact ⟨7,by decide +kernel,by decide +kernel⟩
    · exact ⟨12,by decide +kernel,by decide +kernel⟩
  have sep : ∀ M∈X, M.card=2 ∧ M∉L ∧ ∀ T∈L, ¬M⊆T := by
    intro M hm; simp only [X,Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl | rfl <;> refine ⟨by decide +kernel,by decide +kernel,?_⟩ <;>
      intro T ht <;> simp only [L,Finset.mem_insert,Finset.mem_singleton] at ht <;> rcases ht with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have u := full_cost h hc hz P I (by decide +kernel) hsub L X (by decide +kernel)
    tri distinct hits sep (by decide +kernel)
  have c : P.card=7 ∧ I.card=7 ∧ L.card=5 ∧ X.card=2 := by decide +kernel
  have ec := inelig_card_add 14 D
  rw [←sub] at ec
  change I.card + _ = _ at ec
  omega

open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools

def wide (P : Finset V) := Finset.univ.filter fun i : V => (projected P i).card = 3

def labels (P O : Finset V) := (Finset.univ \ O).biUnion (projected P)

theorem proj_mem (P : Finset V) (i a : V) : a∈projected P i ↔ a∈P ∧ adj i a := Finset.mem_filter

theorem proj_le (P : Finset V) (i : V) : (projected P i).card≤3 := by
  have deg : ∀ j : V, (projected Finset.univ j).card≤3 := by decide +kernel
  exact le_trans (Finset.card_le_card (fun a ha => (proj_mem _ _ a).2 ⟨Finset.mem_univ _,((proj_mem _ _ a).1 ha).2⟩)) (deg i)

theorem proj_meet (P : Finset V) {i j : V} (ne : i≠j) : (projected P i ∩ projected P j).card≤1 := by
  have ff : ∀ i j : V, i≠j → (projected Finset.univ i ∩ projected Finset.univ j).card≤1 := by decide +kernel
  apply le_trans (Finset.card_le_card _) (ff _ _ ne)
  intro a ha
  rcases Finset.mem_inter.mp ha with ⟨ai,aj⟩
  exact Finset.mem_inter.mpr ⟨(proj_mem _ _ _).2 ⟨Finset.mem_univ _,((proj_mem _ _ _).1 ai).2⟩,
    (proj_mem _ _ _).2 ⟨Finset.mem_univ _,((proj_mem _ _ _).1 aj).2⟩⟩

noncomputable def marks (D : Dag) (P : Finset V) : Finset V := by
  classical
  exact (wide P).filter (fun i => sup_Occ 14 D P (projected P i))

theorem mark_iff {D : Dag} {P : Finset V} {i : V} : i∈marks D P ↔ (projected P i).card=3 ∧ sup_Occ 14 D P (projected P i) := by
  classical
  simp [marks,wide]

theorem projected_count {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (P : Finset V)
    (hind : independent P) (p7 : P.card ≤ 7) :
    2*(marks D P).card + (ineligSet 14 D ∩ wide P).card + (labels P (marks D P)).card + (eligSet 14 D).card ≤
    P.card + (P ∩ eligSet 14 D).card + Bplus 14 D := by
  classical
  let O := marks D P
  let W := ineligSet 14 D ∩ wide P
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨E,ne,he⟩ := sup_assigned_exits graph_ok h hc P W (fun i hi => by
    rcases Finset.mem_inter.mp hi with ⟨hin,wi⟩
    have three : (projected P i).card=3 := by simpa [wide] using wi
    exact ⟨hin,projected P i,Finset.filter_subset _ _,by omega,fun a ha => ((proj_mem _ _ a).1 ha).2⟩)
  have each : ∀ f ∈ labels P O, ∃ c, c∉O ∧ f∈projected P c := by
    intro f hf; obtain ⟨c,hc,hf⟩ := Finset.mem_biUnion.mp hf
    exact ⟨c,(Finset.mem_sdiff.mp hc).2,hf⟩
  choose! c chooseC using each
  have src (f) (hf : f∈labels P O) : ∃ e, sup_Wit 14 D P (projected P (c f)) f e := by
    let v := c f
    let U := projected P v
    have inside : U⊆P := Finset.filter_subset _ _
    have cov : U.card≤2 ∨ U.card=3 ∧ ¬sup_Occ 14 D P U := by
      have small := proj_le P v
      by_cases t : U.card=3
      · exact Or.inr ⟨t,fun occ => (chooseC _ hf).1 (mark_iff.2 ⟨t,occ⟩)⟩
      · change U.card≤3 at small
        exact Or.inl (by omega)
    let X := insert v (P \ U)
    refine sup_wit_exists graph_ok h.1 hc (X:=X) inside cov ?_ (fun a ha => Finset.mem_insert_of_mem ha)
      (chooseC _ hf).2 ⟨v,Finset.mem_insert_self _ _,graph_ok.1 _ _ ((proj_mem _ _ _).1 (chooseC _ hf).2).2⟩
    have no (a) (ha : a ∈ P \ U) : ¬adj v a := fun ev => (Finset.mem_sdiff.mp ha).2 ((proj_mem P v a).2 ⟨(Finset.mem_sdiff.mp ha).1,ev⟩)
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with rfl|hi <;> rcases Finset.mem_insert.mp hj with rfl|hj
    · exact graph_ok.2.1 _
    · exact no _ hj
    · exact fun a => no _ hi (graph_ok.1 _ _ a)
    · exact hind _ (Finset.mem_sdiff.mp hi).1 _ (Finset.mem_sdiff.mp hj).1
  have main := cnt_main h.1 p7 (O.image (projected P)) (fun T ht => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht; exact mark_iff.mp hi)
    (fun T ht U hu neq => by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hu
      exact proj_meet P (fun e => neq (congrArg (projected P) e)))
    E he (labels P O) (fun f => projected P (c f)) src (fun f hf T ht => by
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
      exact proj_meet P (fun eq => (chooseC _ hf).1 (eq ▸ hi)))
  have inj : Set.InjOn (projected P) O := by
    intro u hu v hv eq
    by_contra bad
    have small := proj_meet P bad
    rw [eq,Finset.inter_self] at small
    have full := (mark_iff.mp hv).1
    omega
  rw [Finset.card_image_of_injOn inj,ne] at main
  have fl := carrier_flow_union h P (by rw [sem_supp_out graph_ok hc];simp)
  have sup := surplus_carrierT_le h.1 b hb P
  change 2*O.card+W.card+(labels P O).card+(eligSet 14 D).card ≤ P.card+(P ∩ eligSet 14 D).card+Bplus 14 D
  omega



abbrev WeightSpec := Nat × Nat × Nat × Nat × Nat × Nat × Nat

def weightKey (r : WeightSpec) := (r.1,r.2.2.2.1)

def weightWitness (a : Nat) (v : V) := mask ((a >>> (14*v.val)) &&& 16383)

def point (p j : Nat) : V := Fin.ofNat 14 ((p >>> (4*j)) &&& 15)

def weightGeometry (K T : Finset V) (m p : Nat) : Prop :=
  let i := point p 0
  let j := point p 1
  let x := point p 2
  let y := point p 3
  let z := point p 4
  m=0 ∨ (m=1 ∧ i∈K ∧ adj i x ∧ adj i y ∧ x∈T ∧ y∈T ∧ x≠y) ∨
    (m=2 ∧ i∈K ∧ j∈K ∧ adj i x ∧ adj i y ∧ adj j x ∧ adj j z ∧ T.card=3 ∧ x∈T ∧ y∈T ∧ z∈T ∧ x≠y ∧ x≠z ∧ y≠z)

instance (K T : Finset V) (m p : Nat) : Decidable (weightGeometry K T m p) := by unfold weightGeometry; infer_instance

def weightValid (r : WeightSpec) :=
  let (K,T,J,k,m,p,a) := r
  decide (ValidPrivate (mask T) (mask J) (weightWitness a) ∧ mask J ⊆ mask K ∧ k+(mask T).card ≤ (mask J).card+m ∧ weightGeometry (mask K) (mask T) m p)

theorem geometricCost {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (K T : Finset V)
    (m p : Nat) (geom : weightGeometry K T m p) (sub : K⊆ineligSet 14 D) : m≤cost D T := by
  rcases geom with rfl|⟨rfl,i,rest⟩|⟨rfl,i,j,rest⟩
  · exact Nat.zero_le _
  · exact cost_one h hc T (point p 0) (point p 2) (point p 3) (sub i) rest
  · exact cost_two h hc T (point p 0) (point p 1) (point p 2) (point p 3) (point p 4) (sub i) (sub j) rest

theorem compact_weight {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (r : WeightSpec)
    (ok : weightValid r=true) (sub : mask (weightKey r).1 ⊆ ineligSet 14 D) :
    (eligSet 14 D).card+(weightKey r).2 ≤ Bplus 14 D := by
  rcases r with ⟨K,T,J,k,m,p,a⟩
  obtain ⟨valid,small,size,geom⟩ := of_decide_eq_true ok
  exact bound_rule h hc (mask T) (mask J) (weightWitness a) valid (small.trans sub) m k
    (geometricCost h hc (mask K) (mask T) m p geom sub) size

end PEqualNP.Outside.L_meta_9775.UpstreamCore
