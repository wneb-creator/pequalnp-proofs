namespace PEqualNP.Outside.L_meta_3754.Positive
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core

lemma unique_dirty_positive_impossible {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (g : ℕ)
    (hcolor : ∀a b : Fin n,G.Adj a b → s a≠s b) (hcycle : NoFourCycle G)
    (hC : IsLeastAO G C) (hfixed : IsLiftFixedPoint G C)
    (hg : g<C.gates.length) (hand : (gateAt C g).op=GateOp.and)
    (hdirty : ¬BelowF G C g)
    (hclean : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → k≠g → BelowF G C k)
    (hunit : ∃v : Fin n,gateVal n C g (PEqualNP.SplitCount.unitInput v)=true) : False := by
  have hne := Deletion.least_has_edge_of_gate G C hC g hg
  have hcones := Deletion.least_inOutputCone hC hne
  have hout := (Deletion.output_bounds hC hne).2
  have hnoimp : ∀k<C.gates.length,(gateAt C k).op=GateOp.and →
      ∀t∈(gateAt C k).inputs,¬∀x : Fin n → Bool,
        Circuit.eval ⟨C.gates,t⟩ (List.ofFn x)=true → graphFun G ∅ x=true := by
    intro k hk hkAND t ht
    exact Bypass.least_no_and_below_operand hC hk hkAND ht
  obtain ⟨aW,bW,v,m,E⟩ := Strict3653.least_exceptional n G C s g hcolor hcycle hC hfixed
    hnoimp hcones hg hand hdirty hclean hunit
  obtain ⟨j,p,u,hjg,hjor,hp,hjin,hpv,huv,hpu,huA,hum,hjv,hju,hjB,hjnb,hpB⟩ :=
    Glue.select_exception G C s g aW bW v m hC hfixed (hcones g hg) hdirty hclean E
  let P := Bypass.patchThree C j p (bW-n) g v.val
  have hP : IsAO2 n P := Bypass.patchThree_isAO2 hC.1 j p (bW-n) g v.val hp v.isLt
  have hlen : P.gates.length=C.gates.length := Bypass.patchThree_length C j p (bW-n) g v.val
  have hsem : PatchSemantics.AliasSem n C P j p (bW-n) g v :=
    Bypass.patchThree_semantics hC.1 j p (bW-n) g v hp
  have hpair : wireVal n P C.output (pairInput v m)=true :=
    ExceptionalPair.exceptional_alias_pair G C P s hC hfixed g aW bW v m E j p hjg
      hsem hout hcones hclean hjv
  have hnoimpOpnd : ∀k<C.gates.length,(gateAt C k).op=GateOp.and → ∀b : Fin 2,
      ¬∀x : Fin n → Bool,wireVal n C (opnd C k b) x=true → graphFun G ∅ x=true := by
    intro k hk hkAND b
    exact PairPreserve.noimp G C hC k hk hkAND b
  have hrestore := PatchSemantics.exceptional_restoration G hcycle s hcolor C P hC.1 hP
    hC.2.1 hlen hfixed g aW bW v m hg E hcones hclean hnoimpOpnd j p u hjg hjor hp
    hjin huv huA hjv hju hout hsem hpair
  have hBg : bW-n<g := by have := E.bBound;have := E.bGate;omega
  apply Bypass.patch_three_strict_saving hC j p (bW-n) g aW v m hjg hBg hg hjB hp
    (E.aBound.trans (Nat.add_lt_add_left hg n)) hout
  intro x
  change (wireVal n P C.output x || (x m && wireVal n P aW x))=graphFun G ∅ x
  exact hrestore x

end PEqualNP.Outside.L_meta_3754.Positive
