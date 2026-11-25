import UpstreamGraph
namespace PEqualNP.Outside.L_meta_9775.UpstreamCore
open DagTools
set_option maxHeartbeats 0 in
theorem partial_exits {n : Nat} {G : Fin n → Fin n → Prop} {D : Dag} (hG : sem_Gr G) (hS : Strict n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hpos : k4_Pos n G D pos) (T J Q : Finset (Fin n)) (qsub : Q ⊆ T)
    (A : Fin n → Finset (Fin n))
    (hJ : ∀ i ∈ J, i ∈ ineligSet n D ∧ (∃ a ∈ T, G i a) ∧ ∀ f ∈ Q, ∃ a ∈ A f, G i a)
    (hA : ∀ f ∈ Q, (∀ a ∈ A f, ∀ b ∈ A f, ¬ G a b) ∧ T.erase f ⊆ A f ∧ ∃ a ∈ A f, G f a) :
    J.card + Q.card ≤ (exitArcs n D (carrierT n D T)).card := by
  classical
  obtain ⟨hsub, hcard⟩ := k4_exits_ge hpos T J (fun i hi => ⟨(hJ i hi).1, (hJ i hi).2.1⟩)
  have hex : ∀ f ∈ Q, ∃ e : ℕ × Bool, e.1 < D.length ∧ tag D e.1 = true ∧
      f ∈ supp n D (src D e) ∧ f ∉ supp n D (n + e.1) ∧ Disjoint (supp n D (src D e)) (A f) := by
    intro f hf
    obtain ⟨j, s, h1, h2, h4, h5, h6⟩ := sem_exposure hG hS hC (A f) (hA f hf).1 f (hA f hf).2.2
    exact ⟨(j, s), h1, h2, h4, h5, h6⟩
  choose! w hw using hex
  have hinj : Set.InjOn w Q := by
    intro f hf g hg hfg
    by_contra hne
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2 (hfg ▸ (hw g hg).2.2.1)
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => hne h.symm, qsub hg⟩))
  have hdis : Disjoint (J.image pos) (Q.image w) := by
    rw [Finset.disjoint_left]
    intro e he1 he2
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 he1
    obtain ⟨f, hf, hfe⟩ := Finset.mem_image.1 he2
    obtain ⟨a, ha, hia⟩ := (hJ i hi).2.2 f hf
    exact Finset.disjoint_left.1 (hw f hf).2.2.2.2
      (hfe ▸ (hpos.1 i (hJ i hi).1).2.2.1 a hia) ha
  have hsub2 : Q.image w ⊆ exitArcs n D (carrierT n D T) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨h1, h2, h4, h5, h6⟩ := hw f hf
    refine k4_mem_exit.2 ⟨h1, ⟨f, Finset.mem_inter.2 ⟨h4, qsub hf⟩⟩, ?_⟩
    rintro ⟨g, hg⟩
    rw [Finset.mem_inter] at hg
    have hgs : g ∈ supp n D (src D (w f)) := sem_supp_and_sub hS h1 h2 (w f).2 hg.1
    exact Finset.disjoint_left.1 h6 hgs
      ((hA f hf).2.1 (Finset.mem_erase.2 ⟨fun h => h5 (h ▸ hg.1), hg.2⟩))
  have := Finset.card_le_card (Finset.union_subset hsub hsub2)
  rw [Finset.card_union_of_disjoint hdis, hcard, Finset.card_image_of_injOn hinj] at this
  exact this

set_option maxHeartbeats 0 in
theorem local_merge {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (zero : Bzero 14 D = 0) (P I U W : Finset V) (ind : independent P) (p7 : P.card ≤ 7)
    (sub : I ⊆ ineligSet 14 D) (u : ∀ i ∈ U, i ∈ I ∧ (projected P i).card=3)
    (w : ∀ i ∈ W, i ∈ I ∧ (projected P i).card=2) :
    2*U.card+W.card ≤ (merges 14 D (carrierT 14 D P)).card := by
  let f := projected P
  have sep {i j : V} (ne : i≠j) : (f i ∩ f j).card≤1 := proj_meet P ne
  have inj {T : Finset V} (hi : ∀ i∈T, 2≤(f i).card) : Set.InjOn f T := by
    intro i iT j _ eq
    by_contra ne
    have le := sep ne
    rw [←eq,Finset.inter_self] at le
    have := hi i iT
    omega
  have uinj : Set.InjOn f U := inj (fun i hi => by have := (u i hi).2; change 2≤(projected P i).card; omega)
  have winj : Set.InjOn f W := inj (fun i hi => (w i hi).2.ge)
  have m := sup_charge h.1 p7 (U.image f) (fun T ht => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(u _ hi).2,occurs h hc zero P ind i (sub (u _ hi).1)⟩) (fun T ht M hm diff => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hm
    exact sep (fun e => diff (congrArg f e))) (W.image f) (fun M hm => by
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hm
    have c : (f i).card=2 := (w i hi).2
    have separate : ∀ j∈U, ¬f i ⊆ f j := by
      intro j hj incl
      have cj : (f j).card=3 := (u j hj).2
      have distinct : i≠j := by rintro rfl; omega
      have v := sep distinct
      rw [Finset.inter_eq_left.mpr incl,c] at v
      omega
    refine ⟨occurs h hc zero P ind i (sub (w _ hi).1),by omega,?_,by omega,by omega,?_⟩
    · intro mem
      obtain ⟨j,hj,eq⟩ := Finset.mem_image.mp mem
      exact separate j hj (by rw [eq])
    · intro _ T ht
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
      exact separate j hj)
  rw [Finset.card_image_of_injOn uinj,Finset.card_image_of_injOn winj] at m
  exact m.trans (Finset.card_le_card (Finset.filter_subset _ _))

set_option maxHeartbeats 0 in
theorem private_bound {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (zero : Bzero 14 D=0) (P I U W J Q : Finset V) (A : V → Finset V)
    (eq : I=ineligSet 14 D) (ind : independent P) (p7 : P.card≤7) (qs : Q⊆P)
    (u : ∀ i∈U, i∈I ∧ (projected P i).card=3) (w : ∀ i∈W, i∈I ∧ (projected P i).card=2)
    (j : ∀ i∈J, i∈I ∧ (∃ a ∈ P, adj i a) ∧ ∀ f ∈ Q, ∃ a ∈ A f, adj i a)
    (free : ∀ f∈Q, independent (A f) ∧ P.erase f ⊆ A f ∧ ∃ a∈A f, adj f a) :
    J.card+Q.card+2*U.card+W.card+(14-I.card) ≤ P.card+(P \ I).card+Bplus 14 D := by
  obtain ⟨b,hb⟩ := sem_exists_pureBranch graph_ok h.1 hc
  obtain ⟨pos,hpos⟩ := k4_assigned graph_ok h hc
  have lo := local_merge h hc zero P I U W ind p7 (eq ▸ Finset.Subset.rfl) u w
  have exits := partial_exits graph_ok h.1 hc hpos P J Q qs A
    (fun i hi => ⟨eq ▸ (j i hi).1,(j i hi).2⟩) free
  have fl := carrier_flow_union h P (by rw [sem_supp_out graph_ok hc];simp)
  have sup := surplus_carrierT_le h.1 b hb P
  have card := inelig_card_add 14 D
  have seteq : P \ I = P ∩ eligSet 14 D := by
    ext x
    simp [eq,sem_mem_inelig]
  rw [seteq,eq]
  omega
set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection55 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 55=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 55) (mask 0) (mask 21) (mask 55) (mask 256)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 55).card+(mask 256).card+2*(mask 0).card+(mask 21).card+(14-(mask 55).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 55).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection95 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 95=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11008) (mask 95) (mask 64) (mask 22) (mask 95) (mask 512)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 10656, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 95).card+(mask 512).card+2*(mask 64).card+(mask 22).card+(14-(mask 95).card)=20 := by decide +kernel
  have rhs : (mask 11008).card+(mask 11008 \ mask 95).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection103 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 103=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 1792) (mask 103) (mask 0) (mask 97) (mask 103) (mask 1024)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 792, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 103).card+(mask 1024).card+2*(mask 0).card+(mask 97).card+(14-(mask 103).card)=18 := by decide +kernel
  have rhs : (mask 1792).card+(mask 1792 \ mask 103).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection119 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 119=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 12032) (mask 119) (mask 80) (mask 39) (mask 119) (mask 2048)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9992, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 119).card+(mask 2048).card+2*(mask 80).card+(mask 39).card+(14-(mask 119).card)=23 := by decide +kernel
  have rhs : (mask 12032).card+(mask 12032 \ mask 119).card=10 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection123 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 123=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3840) (mask 123) (mask 64) (mask 49) (mask 123) (mask 256)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 7812, 0, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 123).card+(mask 256).card+2*(mask 64).card+(mask 49).card+(14-(mask 123).card)=20 := by decide +kernel
  have rhs : (mask 3840).card+(mask 3840 \ mask 123).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection181 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 181=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 181) (mask 0) (mask 21) (mask 53) (mask 8448)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 0, 0, 0, 1290] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 53).card+(mask 8448).card+2*(mask 0).card+(mask 21).card+(14-(mask 181).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 181).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection229 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 229=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 1792) (mask 229) (mask 0) (mask 97) (mask 101) (mask 1536)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 1290, 792, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 101).card+(mask 1536).card+2*(mask 0).card+(mask 97).card+(14-(mask 229).card)=18 := by decide +kernel
  have rhs : (mask 1792).card+(mask 1792 \ mask 229).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 245=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 3840) (mask 245) (mask 64) (mask 49) (mask 117) (mask 2560)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 7426, 0, 9992, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 117).card+(mask 2560).card+2*(mask 64).card+(mask 49).card+(14-(mask 245).card)=20 := by decide +kernel
  have rhs : (mask 3840).card+(mask 3840 \ mask 245).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection661 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 661=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 661) (mask 0) (mask 21) (mask 21) (mask 9472)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 8488, 0, 0, 1290] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 21).card+(mask 9472).card+2*(mask 0).card+(mask 21).card+(14-(mask 661).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 661).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection2693 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 2693=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 74) (mask 2693) (mask 0) (mask 2688) (mask 2688) (mask 74)
    (fun f : V => mask (([0, 8297, 0, 4183, 0, 0, 314, 0, 0, 0, 0, 0, 0, 0] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 2688).card+(mask 74).card+2*(mask 0).card+(mask 2688).card+(14-(mask 2693).card)=18 := by decide +kernel
  have rhs : (mask 74).card+(mask 74 \ mask 2693).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection4245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 4245=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 9472) (mask 4245) (mask 0) (mask 21) (mask 21) (mask 9472)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 9288, 0, 8488, 0, 0, 1290] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 21).card+(mask 9472).card+2*(mask 0).card+(mask 21).card+(14-(mask 4245).card)=18 := by decide +kernel
  have rhs : (mask 9472).card+(mask 9472 \ mask 4245).card=6 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection4309 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 4309=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 11520) (mask 4309) (mask 16) (mask 69) (mask 85) (mask 11264)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 10656, 9992, 0, 7426] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 85).card+(mask 11264).card+2*(mask 16).card+(mask 69).card+(14-(mask 4309).card)=20 := by decide +kernel
  have rhs : (mask 11520).card+(mask 11520 \ mask 4309).card=8 := by decide +kernel
  omega

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem projection5190 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D)
    (z : Bzero 14 D=0) (eq : mask 5190=ineligSet 14 D) : 12≤Bplus 14 D := by
  have v := private_bound h hc z (mask 8960) (mask 5190) (mask 0) (mask 70) (mask 70) (mask 8960)
    (fun f : V => mask (([0, 0, 0, 0, 0, 0, 0, 0, 8713, 8488, 0, 0, 0, 792] : List Nat).getD f.val 0)) eq
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have lhs : (mask 70).card+(mask 8960).card+2*(mask 0).card+(mask 70).card+(14-(mask 5190).card)=18 := by decide +kernel
  have rhs : (mask 8960).card+(mask 8960 \ mask 5190).card=6 := by decide +kernel
  omega


end PEqualNP.Outside.L_meta_9775.UpstreamCore
