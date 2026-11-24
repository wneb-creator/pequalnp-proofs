namespace PEqualNP.Outside.L_meta_1477.SingletonPairIntegration
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership OneJunk TwoProductCentreless

lemma plane_equal_or_opposite_size [DecidableRel planeGraph.Adj]
    (C : Circuit) (hL : IsLeastAO planeGraph C) (hTF : TopForm planeGraph C)
    (g h : ℕ) (hjunk : junk planeGraph C={g,h}) (hgh : g≠h)
    (hpureg : ∀b : Fin 2,∀k<C.gates.length,(gateAt C k).op=GateOp.and→¬P2.OrR 42 C (opnd C g b) (42+k))
    (hpureh : ∀b : Fin 2,∀k<C.gates.length,(gateAt C k).op=GateOp.and→¬P2.OrR 42 C (opnd C h b) (42+k))
    (a b : Fin 42) (hsingleg : side (n := 42) C g 0={a}) (hsingleh : side (n := 42) C h 0={b})
    (hdisg : Disjoint (side (n := 42) C g 0) (side C g 1))
    (hdish : Disjoint (side (n := 42) C h 0) (side C h 1))
    (hab : a=b ∨ TwoProductCentreless.planeColor a≠TwoProductCentreless.planeColor b)
    (hnojoint : ∀u v : Fin 42,gateVal 42 C g (pairInput u v)=true→
      gateVal 42 C h (pairInput u v)=true→¬GeneralDirtyPairs.JointClean planeGraph C g h) :
    125≤C.size := by
  have hE : planeGraph.edgeFinset.card=105 := planeGraph_card
  have hne : planeGraph.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  have hb := equal_or_opposite_lower_bound planeGraph plane_no_four planeColor planeColor_proper
    C hL hTF hne 21 (fun K hK => planeGraph_cover_lower K (fun u v huv => hK huv))
    g h hjunk hgh hpureg hpureh a b hsingleg hsingleh hdisg hdish hab hnojoint
  omega

end PEqualNP.Outside.L_meta_1477.SingletonPairIntegration
