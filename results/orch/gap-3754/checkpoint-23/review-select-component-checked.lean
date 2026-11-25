namespace PEqualNP.Outside.L_meta_3754.Select
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma or_cone_forward (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∀k,k<C.gates.length → (gateAt C k).op=GateOp.or →
      (∀i,InCone n C i k → (gateAt C i).op=GateOp.or) →
      ∀j,(j=k ∨ InCone n C j k) → ∀x : Fin n → Bool,
      wireVal n C (n+j) x=true → wireVal n C (n+k) x=true := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hop hall j hreach x hx
    rcases hreach with rfl | hreach
    · exact hx
    obtain ⟨w,hw,hnw,hwk,hj⟩ := (Ledger.inCone_iff n C j k hk).mp hreach
    have ht : w-n<k := by omega
    have htk : InCone n C (w-n) k :=
      (Ledger.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hnw,hwk,Or.inl rfl⟩
    have hv := ih (w-n) ht (by omega) (hall _ htk)
      (fun i hi => hall i (Ledger.inCone_trans n C i (w-n) k hk hi htk)) j hj x hx
    apply Ledger.wire_or_true n C hAO k hk hop w hw x
    simpa only [show n+(w-n)=w by omega] using hv

lemma singleton_raw_reader (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (v : Fin n) :
    ∀k,k<C.gates.length → (gateAt C k).op=GateOp.or →
      (∀i,InCone n C i k → (gateAt C i).op=GateOp.or) →
      wireVal n C (n+k) (Ledger.singletonInput v)=true →
      ∃j,j≤k ∧ (j=k ∨ InCone n C j k) ∧ (gateAt C j).op=GateOp.or ∧
        v.val∈(gateAt C j).inputs := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hop hall hx
    rw [Ledger.wireVal_gate n C _ k hk hAO.2.1,hop] at hx
    simp only [GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hx
    obtain ⟨w,hw,hwv⟩ := hx
    have hwk := hAO.2.1 k hk w hw
    by_cases hwn : w<n
    · have he : (⟨w,hwn⟩ : Fin n)=v := by
        simpa [Ledger.wireVal_input n C _ w hwn,Ledger.singletonInput] using hwv
      have heval : w=v.val := congrArg Fin.val he
      exact ⟨k,le_refl _,Or.inl rfl,hop,heval ▸ hw⟩
    · have hnk : n≤w := by omega
      have ht : w-n<k := by omega
      have htk : InCone n C (w-n) k :=
        (Ledger.inCone_iff n C (w-n) k hk).mpr ⟨w,hw,hnk,hwk,Or.inl rfl⟩
      have hwv' : wireVal n C (n+(w-n)) (Ledger.singletonInput v)=true := by
        simpa only [show n+(w-n)=w by omega] using hwv
      obtain ⟨j,hj,hreach,hjor,hjv⟩ := ih (w-n) ht (by omega) (hall _ htk)
        (fun i hi => hall i (Ledger.inCone_trans n C i (w-n) k hk hi htk)) hwv'
      refine ⟨j,by omega,Or.inr ?_,hjor,hjv⟩
      rcases hreach with rfl | hreach
      · exact htk
      · exact Ledger.inCone_trans n C j (w-n) k hk hreach htk

lemma direct_other (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (v : Fin n) (hv : v.val∈(gateAt C j).inputs) :
    ∃p,p<n+j ∧ ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) := by
  obtain ⟨a,b,hab⟩ := Ledger.gate_two n C hAO j hj
  have hva : v.val=a ∨ v.val=b := by simpa [hab] using hv
  rcases hva with h | h
  · refine ⟨b,hAO.2.1 j hj b (by simp [hab]),Or.inl ?_⟩
    simpa only [h] using hab
  · refine ⟨a,hAO.2.1 j hj a (by simp [hab]),Or.inr ?_⟩
    simpa only [h] using hab

lemma direct_or_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hop : (gateAt C j).op=GateOp.or) (v : Fin n) (p : ℕ)
    (hin : (gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) (x : Fin n → Bool) :
    wireVal n C (n+j) x=(x v || wireVal n C p x) := by
  rw [Ledger.wireVal_gate n C x j hj hAO.2.1,hop]
  rcases hin with hin | hin
  · simp [hin,GateOp.eval,Ledger.wireVal_input n C x v.val v.isLt]
  · simp [hin,GateOp.eval,Ledger.wireVal_input n C x v.val v.isLt,Bool.or_comm]

lemma direct_other_excludes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (j : ℕ) (hj : j<C.gates.length)
    (hop : (gateAt C j).op=GateOp.or) (v : Fin n) (p : ℕ) (hp : p<n+j)
    (hin : (gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) :
    wireVal n C p (Ledger.singletonInput v)=false := by
  cases hv : wireVal n C p (Ledger.singletonInput v)
  · rfl
  · exfalso
    apply Bypass.least_no_equal_earlier hC hj hp
    intro x
    change wireVal n C (n+j) x=wireVal n C p x
    rw [direct_or_value n C hC.1 j hj hop v p hin x]
    have hsub : x v=true → wireVal n C p x=true := by
      intro hx
      apply Ledger.wire_monotone n C hC.1 (Ledger.singletonInput v) x _ p (by omega) hv
      intro i hi
      have he : i=v := by simpa [Ledger.singletonInput] using hi
      simpa only [he] using hx
    cases hx : x v <;> cases hpx : wireVal n C p x <;> simp_all

lemma or_operand_witness (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j<C.gates.length) (hall : ∀i,InCone n C i j → (gateAt C i).op=GateOp.or)
    (p : ℕ) (hpm : p∈(gateAt C j).inputs) (x : Fin n → Bool) (hpx : wireVal n C p x=true) :
    ∃u : Fin n,x u=true ∧ wireVal n C p (Ledger.singletonInput u)=true := by
  have hpj := hAO.2.1 j hj p hpm
  by_cases hpn : p<n
  · refine ⟨⟨p,hpn⟩,?_,?_⟩
    · simpa only [Ledger.wireVal_input n C x p hpn] using hpx
    · rw [Ledger.wireVal_input n C _ p hpn]
      simp [Ledger.singletonInput]
  · have hnp : n≤p := by omega
    have hpk : p-n<j := by omega
    have hpc : InCone n C (p-n) j :=
      (Ledger.inCone_iff n C (p-n) j hj).mpr ⟨p,hpm,hnp,hpj,Or.inl rfl⟩
    have hpx' : wireVal n C (n+(p-n)) x=true := by simpa only [show n+(p-n)=p by omega] using hpx
    obtain ⟨u,hu,hup⟩ := Ledger.or_cone_singleton_witness n C hAO (p-n) (by omega) (hall _ hpc)
      (fun i hi => hall i (Ledger.inCone_trans n C i (p-n) j hj hi hpc)) x hpx'
    exact ⟨u,hu,by simpa only [show n+(p-n)=p by omega] using hup⟩

lemma select_in_or_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (k : ℕ) (hk : k<C.gates.length)
    (hop : (gateAt C k).op=GateOp.or)
    (hall : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or)
    (v : Fin n) (hv : v∈Ledger.singletonSupport n C (n+k)) :
    ∃ (j p : ℕ) (u : Fin n),j≤k ∧ (j=k ∨ InCone n C j k) ∧
      (gateAt C j).op=GateOp.or ∧ p<n+j ∧
      ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) ∧
      wireVal n C p (Ledger.singletonInput v)=false ∧ u≠v ∧
      wireVal n C p (Ledger.singletonInput u)=true ∧
      u∈Ledger.singletonSupport n C (n+k) ∧
      wireVal n C (n+j) (Ledger.singletonInput v)=true ∧
      wireVal n C (n+j) (Ledger.singletonInput u)=true := by
  obtain ⟨j,hjk,hreach,hjor,hjv⟩ := singleton_raw_reader n C hC.1 v k hk hop hall
    (Finset.mem_filter.mp hv).2
  have hj : j<C.gates.length := by omega
  obtain ⟨p,hp,hin⟩ := direct_other n C hC.1 j hj v hjv
  have hpfalse := direct_other_excludes G C hC j hj hjor v p hp hin
  have hpm : p∈(gateAt C j).inputs := by rcases hin with hin | hin <;> simp [hin]
  have hjall : ∀i,InCone n C i j → (gateAt C i).op=GateOp.or := by
    intro i hi
    rcases hreach with rfl | hreach
    · exact hall i hi
    · exact hall i (Ledger.inCone_trans n C i j k hk hi hreach)
  obtain ⟨u,_,hpu⟩ := or_operand_witness n C hC.1 j hj hjall p hpm (fun _ => true)
    (Ledger.wire_all_true n C hC.1 p (by omega))
  have huv : u≠v := by intro he;subst u;rw [hpfalse] at hpu;cases hpu
  have hjut : wireVal n C (n+j) (Ledger.singletonInput u)=true := by
    rw [direct_or_value n C hC.1 j hj hjor v p hin]
    simp [hpu]
  have hju : u∈Ledger.singletonSupport n C (n+k) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,or_cone_forward n C hC.1 k hk hop hall j hreach _ hjut⟩
  refine ⟨j,p,u,hjk,hreach,hjor,hp,hin,hpfalse,huv,hpu,hju,?_,hjut⟩
  rw [direct_or_value n C hC.1 j hj hjor v p hin]
  simp [Ledger.singletonInput]

lemma selected_outside_second {n : ℕ} (C : Circuit) (hAO : IsAO2 n C)
    (a b j p : ℕ) (hb : b<C.gates.length) (hbor : (gateAt C b).op=GateOp.or)
    (hbanc : ∀i,InCone n C i b → (gateAt C i).op=GateOp.or)
    (v u : Fin n) (huv : u≠v)
    (hinter : Ledger.singletonSupport n C a ∩ Ledger.singletonSupport n C (n+b)={v})
    (huA : u∈Ledger.singletonSupport n C a)
    (hpv : wireVal n C p (Ledger.singletonInput v)=false)
    (hju : wireVal n C (n+j) (Ledger.singletonInput u)=true) :
    j≠b ∧ ¬InCone n C j b ∧ p≠n+b := by
  have huB : u∉Ledger.singletonSupport n C (n+b) := by
    intro huB
    have hu : u∈({v} : Finset (Fin n)) := hinter ▸ Finset.mem_inter.mpr ⟨huA,huB⟩
    exact huv (Finset.mem_singleton.mp hu)
  have hnreach : ¬(j=b ∨ InCone n C j b) := by
    intro hreach
    apply huB
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      or_cone_forward n C hAO b hb hbor hbanc j hreach _ hju⟩
  have hvB : v∈Ledger.singletonSupport n C (n+b) := by
    have hv : v∈Ledger.singletonSupport n C a ∩ Ledger.singletonSupport n C (n+b) := by
      rw [hinter];simp
    exact (Finset.mem_inter.mp hv).2
  refine ⟨fun h => hnreach (Or.inl h),fun h => hnreach (Or.inr h),?_⟩
  intro hp
  subst p
  have hv := (Finset.mem_filter.mp hvB).2
  rw [hpv] at hv
  cases hv

lemma raw_support (n : ℕ) (C : Circuit) (w : ℕ) (hw : w<n) :
    Ledger.singletonSupport n C w={⟨w,hw⟩} := by
  ext u
  simp [Ledger.singletonSupport,Ledger.wireVal_input n C _ w hw,Ledger.singletonInput,eq_comm]

lemma select_pure_operand {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsLeastAO G C) (g : ℕ) (hg : g<C.gates.length)
    (hall : ∀i,InCone n C i g → (gateAt C i).op=GateOp.or)
    (a : ℕ) (ham : a∈(gateAt C g).inputs)
    (hcard : 2≤(Ledger.singletonSupport n C a).card)
    (v : Fin n) (hv : v∈Ledger.singletonSupport n C a) :
    ∃ (j p : ℕ) (u : Fin n),j<g ∧ InCone n C j g ∧
      (gateAt C j).op=GateOp.or ∧ p<n+j ∧
      ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) ∧
      wireVal n C p (Ledger.singletonInput v)=false ∧ u≠v ∧
      wireVal n C p (Ledger.singletonInput u)=true ∧
      u∈Ledger.singletonSupport n C a ∧
      wireVal n C (n+j) (Ledger.singletonInput v)=true ∧
      wireVal n C (n+j) (Ledger.singletonInput u)=true := by
  have hag := hC.1.2.1 g hg a ham
  have hna : n≤a := by
    by_contra hn
    have han : a<n := by omega
    rw [raw_support n C a han,Finset.card_singleton] at hcard
    omega
  let k := a-n
  have hka : n+k=a := by dsimp [k];omega
  have hkg : k<g := by dsimp [k];omega
  have hk : k<C.gates.length := by omega
  have hkcone : InCone n C k g :=
    (Ledger.inCone_iff n C k g hg).mpr ⟨a,ham,hna,hag,Or.inl rfl⟩
  have hkor := hall k hkcone
  have hkall : ∀i,InCone n C i k → (gateAt C i).op=GateOp.or := by
    intro i hi
    exact hall i (Ledger.inCone_trans n C i k g hg hi hkcone)
  obtain ⟨j,p,u,hjk,hreach,hjor,hp,hin,hpv,huv,hpu,huA,hjv,hju⟩ :=
    select_in_or_gate G C hC k hk hkor hkall v (by simpa only [hka] using hv)
  have hjg : InCone n C j g := by
    rcases hreach with rfl | hreach
    · exact hkcone
    · exact Ledger.inCone_trans n C j k g hg hreach hkcone
  exact ⟨j,p,u,by omega,hjg,hjor,hp,hin,hpv,huv,hpu,by simpa only [hka] using huA,hjv,hju⟩

end PEqualNP.Outside.L_meta_3754.Select
