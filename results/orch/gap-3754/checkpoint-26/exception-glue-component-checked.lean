namespace PEqualNP.Outside.L_meta_3754.Glue
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

lemma support_of_pure {n : ℕ} (C : Circuit) (w : ℕ) (A : Finset (Fin n))
    (hpure : ∀x : Fin n → Bool,PEqualNP.ReadTwo.wval C x w=true ↔ ∃u∈A,x u=true) :
    Ledger.singletonSupport n C w=A := by
  ext u
  constructor
  · intro hu
    obtain ⟨v,hv,hvu⟩ := (hpure (Ledger.singletonInput u)).mp (Finset.mem_filter.mp hu).2
    have he : v=u := by simpa [Ledger.singletonInput] using hvu
    simpa only [he] using hv
  · intro hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,(hpure (Ledger.singletonInput u)).mpr ?_⟩
    exact ⟨u,hu,by simp [Ledger.singletonInput]⟩

lemma select_exception {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g aW bW : ℕ) (v m : Fin n)
    (hC : IsLeastAO G C) (hfixed : PEqualNP.Core.IsLiftFixedPoint G C)
    (hcone : PEqualNP.Core.InOutputCone n C g) (hdirty : ¬BelowF G C g)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (e : Strict3653.Exceptional G C s g aW bW v m) :
    ∃(j p : ℕ)(u : Fin n),j<g ∧ (gateAt C j).op=GateOp.or ∧ p<n+j ∧
      ((gateAt C j).inputs=[v.val,p] ∨ (gateAt C j).inputs=[p,v.val]) ∧
      wireVal n C p (Ledger.singletonInput v)=false ∧ u≠v ∧
      wireVal n C p (Ledger.singletonInput u)=true ∧
      u∈Ledger.singletonSupport n C aW ∧ G.Adj u m ∧
      wireVal n C (n+j) (Ledger.singletonInput v)=true ∧
      wireVal n C (n+j) (Ledger.singletonInput u)=true ∧
      j≠bW-n ∧ ¬InCone n C j (bW-n) ∧ p≠bW := by
  have hg : g<C.gates.length := hcone.1
  have hA := support_of_pure C aW (Strict3653.varSet n C g aW) e.pureA
  have hB := support_of_pure C bW (Strict3653.varSet n C g bW) e.pureB
  have hcard : 2≤(Ledger.singletonSupport n C aW).card := by
    rw [hA]
    obtain ⟨u,hu,huv⟩ := e.otherA
    have hsub : ({v,u} : Finset (Fin n))⊆Strict3653.varSet n C g aW := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact e.vInA
      · exact hu
    have hc := Finset.card_le_card hsub
    simpa [huv,Ne.symm huv] using hc
  have hall : ∀i,InCone n C i g → (gateAt C i).op=GateOp.or := by
    intro i hi
    apply Ledger.earliest_dirty_ancestor_or G C hC.1 hfixed g hcone hdirty _ i hi
    intro k hkg hand
    exact hclean k (by omega) hand (by omega)
  obtain ⟨j,p,u,hjg,_,hjor,hp,hin,hpv,huv,hpu,huA,hjv,hju⟩ :=
    Select.select_pure_operand G C hC g hcone.1 hall aW e.aMember hcard v (by rw [hA];exact e.vInA)
  have hb : bW-n<C.gates.length := by have := e.bBound;omega
  have hbeq : n+(bW-n)=bW := by have := e.bGate;omega
  have hbg : InCone n C (bW-n) g :=
    (Ledger.inCone_iff n C (bW-n) g hcone.1).mpr
      ⟨bW,e.bMember,e.bGate,e.bBound,Or.inl rfl⟩
  have hbor : (gateAt C (bW-n)).op=GateOp.or := hall _ hbg
  have hborAnc : ∀i,InCone n C i (bW-n) → (gateAt C i).op=GateOp.or := by
    intro i hi
    exact hall i (Ledger.inCone_trans n C i (bW-n) g hcone.1 hi hbg)
  have hinter : Ledger.singletonSupport n C aW ∩ Ledger.singletonSupport n C (n+(bW-n))={v} := by
    rw [hbeq,hA,hB]
    ext z
    simp only [Finset.mem_inter,Finset.mem_singleton]
    constructor
    · rintro ⟨hzA,hzB⟩
      exact e.sharedOnlyV z hzA hzB
    · intro he
      subst z
      exact ⟨e.vInA,e.vInB⟩
  obtain ⟨hjb,hjnb,hpB⟩ := Select.selected_outside_second C hC.1 aW (bW-n) j p hb hbor
    hborAnc v u huv hinter huA hpv hju
  refine ⟨j,p,u,hjg,hjor,hp,hin,hpv,huv,hpu,huA,?_,hjv,hju,hjb,hjnb,?_⟩
  · exact e.adjacentA u (by rwa [← hA])
  · simpa only [hbeq] using hpB

end PEqualNP.Outside.L_meta_3754.Glue
