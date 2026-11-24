namespace PEqualNP.Outside.L_meta_1477.UniqueAnyCenterPlane

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk Structural StructuralMasks MaskGrouping

set_option maxHeartbeats 1000000 in
lemma unique_center_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hTF : TopForm planeGraph C)
    (hminjunk : ∀D : Circuit,IsLeastAO planeGraph D → (junk planeGraph C).card≤(junk planeGraph D).card)
    (g : Fin 2 → ℕ) (b : Fin 2 → Fin 2) (hjunk : junk planeGraph C={g 0,g 1}) (hneq : g 0≠g 1)
    (hpure : ∀i d,∀k<C.gates.length,(gateAt C k).op=GateOp.and → ¬P2.OrR 42 C (opnd C (g i) d) (42+k))
    (hdis : ∀i,Disjoint (side (n:=42) C (g i) 0) (side C (g i) 1))
    (hlarge : ∀i d,2≤(side (n:=42) C (g i) d).card)
    (p : Fin 42) (hpA : p∈side (n:=42) C (g 0) (b 0))
    (hcenters : cleanCenters planeGraph (side (n:=42) C (g 0) (b 0))
      (side C (g 0) (1-b 0))={p}) : 125≤C.size := by
  classical
  by_contra hnot
  have hsize : C.size≤124 := by omega
  have hAO := P2.ao_of 42 C hL.1
  have hgj (i : Fin 2) : g i∈junk planeGraph C := by fin_cases i <;> rw[hjunk] <;> simp
  have hgdata (i : Fin 2) := (P1.junk_iff planeGraph C (g i)).mp (hgj i)
  have hdisO (i : Fin 2) : Disjoint (side (n:=42) C (g i) (b i)) (side C (g i) (1-b i)) := by
    rcases P2.fin2_sub (b i) with ⟨hb,hb'⟩ | ⟨hb,hb'⟩
    · rw [hb',hb];exact hdis i
    · rw [hb',hb];exact (hdis i).symm
  have hprod (i : Fin 2) (x : Fin 42 → Bool) : gateVal 42 C (g i) x=
      productValue (side (n:=42) C (g i) (b i)) (side C (g i) (1-b i)) x := by
    have hh := ActualCommonMasks.pure_product_value C hAO (g i) (hgdata i).1 (hgdata i).2.1 (hpure i) x
    rcases P2.fin2_sub (b i) with ⟨hb,hb'⟩ | ⟨hb,hb'⟩
    · rw [hb',hb];exact hh
    · rw [hb',hb]
      simpa only [productValue,Bool.and_comm] using hh
  have hpclean : CleanMask planeGraph (side (n:=42) C (g 0) (b 0))
      (side C (g 0) (1-b 0)) p := by
    have hc : p∈cleanCenters planeGraph (side (n:=42) C (g 0) (b 0)) (side C (g 0) (1-b 0)) := by
      rw[hcenters];simp
    exact ((mem_centers_iff _ _ _ _).mp hc).2
  have hpureAll : ∀j∈junk planeGraph C,∀d : Fin 2,∀k<C.gates.length,
      (gateAt C k).op=GateOp.and → ¬P2.OrR 42 C (opnd C j d) (42+k) := by
    intro j hj
    rw[hjunk] at hj
    rcases Finset.mem_insert.mp hj with he | he
    · subst j;exact hpure 0
    · have he := Finset.mem_singleton.mp he
      subst j;exact hpure 1
  have hjointExists : ∃u v : Fin 42,gateVal 42 C (g 0) (pairInput u v)=true ∧
      gateVal 42 C (g 1) (pairInput u v)=true ∧GeneralDirtyPairs.JointClean planeGraph C (g 0) (g 1) := by
    by_contra hn
    have hnoj : ∀j∈junk planeGraph C,g 0≠j → ∀u v : Fin 42,
        gateVal 42 C (g 0) (pairInput u v)=true → gateVal 42 C j (pairInput u v)=true → 
        ¬GeneralDirtyPairs.JointClean planeGraph C (g 0) j := by
      intro j hj hne u v hf0 hfj hjc
      have hj1 : j=g 1 := by
        rw[hjunk] at hj
        rcases Finset.mem_insert.mp hj with he | he
        · exact (hne he.symm).elim
        · exact Finset.mem_singleton.mp he
      subst j
      exact hn ⟨u,v,hf0,hfj,hjc⟩
    have heff := FirstLayerEffective.minimum_junk_two_effective_centers planeGraph C hL hTF
      hminjunk (g 0) (hgj 0) hpureAll hnoj (hdis 0)
    have heq := ActualCleanCenters.effective_centers_eq planeGraph C (g 0)
      (side (n:=42) C (g 0) (b 0)) (side C (g 0) (1-b 0)) (hdisO 0)
      (Finset.card_pos.mp (by have := hlarge 0 (b 0);omega))
      (Finset.card_pos.mp (by have := hlarge 0 (1-b 0);omega)) (hprod 0)
    rw[heq,hcenters,Finset.card_singleton] at heff
    omega
  obtain ⟨u,v,hf0,hf1,hjoint⟩ := hjointExists
  obtain ⟨k,hkroot,hkoutside⟩ := UniqueCenterActual.connector_outside planeGraph PlaneFourClause.plane_noFourCycle
    C hL hminjunk (g 0) (hgj 0) (b 0) p hpA hpclean
    (fun c hc=>by simpa only [hcenters,Finset.mem_singleton] using hc)
    (hdisO 0) (hprod 0) (hlarge 0 (b 0))
  have hcard : (junk planeGraph C).card=2 := by rw[hjunk];exact Finset.card_pair hneq
  have hdisAll : ∀d∈junk planeGraph C,Disjoint (side (n:=42) C d 0) (side C d 1) := by
    intro d hd
    rw[hjunk] at hd
    rcases Finset.mem_insert.mp hd with he | he
    · subst d;exact hdis 0
    · have he := Finset.mem_singleton.mp he
      subst d;exact hdis 1
  have hmask := PlaneTwoJunkPrivate.short_two_junk_all_masked C hL hTF hcard hdisAll hsize
  have hE : planeGraph.edgeFinset.card=105 := planeGraph_card
  have hne : planeGraph.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hJointProduct (x : Fin 42 → Bool)
      (hx : productValue (side (n:=42) C (g 0) (b 0)) (side C (g 0) (1-b 0)) x=true)
      (hy : productValue (side (n:=42) C (g 1) (b 1)) (side C (g 1) (1-b 1)) x=true) :
      ∃a b,planeGraph.Adj a b∧x a=true∧x b=true := by
    have hf := hjoint x ((hprod 0 x).trans hx) ((hprod 1 x).trans hy)
    simpa only [graphFun,Finset.notMem_empty,false_and,exists_false,decide_false,
      Bool.false_or,decide_eq_true_eq] using hf
  have hreader : ∀O : Finset ℕ,(∀k∈O,∀d∈junk planeGraph C,
      ¬P2.OrR 42 C (42+k) (42+d)) → 
      2≤((orN planeGraph C \ lam planeGraph C) \ O).card+2*(centreless planeGraph C).card := by
    intro O hO
    obtain ⟨a₀,ha₀,b₀,hr₀⟩ := FirstLayerEffective.least_dirty_has_top_reader planeGraph C hL (g 0) (hgj 0) hpureAll
    obtain ⟨a₁,ha₁,b₁,hr₁⟩ := FirstLayerEffective.least_dirty_has_top_reader planeGraph C hL (g 1) (hgj 1) hpureAll
    exact OneJunk.two_distinct_dirty_readers planeGraph C hAO (g 0) (g 1) (hgj 0) (hgj 1) hneq
      a₀ a₁ ha₀ ha₁ b₀ b₁ hr₀ hr₁ O hO
  have hcount := UniqueProductBudget.oriented_unique_any_product_lower_bound planeGraph PlaneFourClause.plane_noFourCycle
    C hL hTF hne 21 (fun K hK=>planeGraph_cover_lower K (fun a b hab=>hK hab))
    g b hjunk hneq hpure hdisO (fun i=>hlarge i (b i)) (fun i=>hlarge i (1-b i))
    p hpA hcenters k hkroot hkoutside
    hJointProduct ⟨u,v,(hprod 0 _).symm.trans hf0,(hprod 1 _).symm.trans hf1⟩ hmask hreader
  omega

end PEqualNP.Outside.L_meta_1477.UniqueAnyCenterPlane
